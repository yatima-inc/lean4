// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpTheorems
// Imports: Init Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.DiscrTree Lean.Meta.AppBuilder Lean.Meta.Eqns Lean.Meta.Tactic.AuxLemma
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___closed__2;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_pre___default;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12;
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___closed__4;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22;
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__4;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpTheoremEntry___spec__10(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_keys___default___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_priority___default;
lean_object* l_Lean_Meta_DiscrTree_whnfDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11;
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15(lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorem_perm___default;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_lemmaNames___default;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__17;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24;
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__11;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37;
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_keys___default;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__1;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__19;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_toUnfoldThms___default;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42;
static lean_object* l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add_getName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1;
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__1;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20;
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__6;
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__12;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__1;
static lean_object* l_Lean_Meta_getSimpTheorems___closed__1;
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getName___closed__1;
static lean_object* l_Lean_Meta_SimpTheorem_getName___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteNameMk(lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__1;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072____spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__17;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__8;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__20;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__4;
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167_(lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11___boxed(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34;
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1(lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__3;
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__7;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erased___default;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
lean_object* lean_name_append_after(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__7;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_name_x3f___default;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
static lean_object* l_Lean_Meta_SimpTheorems_pre___default___closed__1;
static lean_object* l_Lean_Meta_mkSimpExt___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5;
static lean_object* l_Lean_Meta_mkSimpExt___closed__2;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToMessageDataSimpTheorem(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__5;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add_getName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__18;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__15;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_post___default;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorem;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__2;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_toUnfold___default;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1;
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10;
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19;
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__6;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorem_post___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__16;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtensionMapRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerSimpAttr___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__3;
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2;
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_getEqnsFor_x3f___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1;
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheorems(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_commandRegister__simp__attr_________closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11;
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44;
lean_object* l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__14;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpEntry;
static lean_object* l_Lean_Meta_instInhabitedSimpEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072____spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_levelParams___default;
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38;
LEAN_EXPORT lean_object* l_Lean_Meta_commandRegister__simp__attr______;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
static lean_object* _init_l_Lean_Meta_SimpTheorem_keys___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_keys___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_levelParams___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_priority___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000u);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SimpTheorem_post___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SimpTheorem_perm___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_name_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint64_t _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_3 = l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = 0;
x_6 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<unknown>");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SimpTheorem_getName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SimpTheorem_getName___closed__2;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SimpTheorem_getName(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":perm");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = l_Lean_Meta_SimpTheorem_getName(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Nat_repr(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_instToFormatSimpTheorem___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_instToFormatSimpTheorem___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
if (x_2 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Meta_instToFormatSimpTheorem___closed__6;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToMessageDataSimpTheorem(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = l_Lean_Meta_SimpTheorem_getName(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Nat_repr(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_instToFormatSimpTheorem___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_instToFormatSimpTheorem___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Meta_instToFormatSimpTheorem___closed__6;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqSimpTheorem(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_pre___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_pre___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpTheorems_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_post___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpTheorems_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_lemmaNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_toUnfold___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erased___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__1;
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
x_3 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_2, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_89_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_expr_eqv(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpTheoremEntry___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_nat_add(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
lean_inc(x_5);
x_13 = lean_array_get(x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_7, 0);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_5);
x_18 = lean_array_get_size(x_6);
x_19 = lean_nat_dec_lt(x_12, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_array_fget(x_6, x_12);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_6, x_12, x_21);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_4);
x_29 = lean_array_fset(x_22, x_12, x_20);
lean_dec(x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_3, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_12, x_34);
lean_dec(x_12);
return x_35;
}
}
}
else
{
x_9 = x_12;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_12, x_8);
if (x_37 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_44 = l_Array_insertAt___rarg(x_6, x_43, x_42);
lean_dec(x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_10 = lean_array_get(x_5, x_6, x_9);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_lt(x_9, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_6, x_9);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_6, x_9, x_18);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_24, x_21);
lean_dec(x_24);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_4);
x_26 = lean_array_fset(x_19, x_9, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_29, x_27);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_fset(x_19, x_9, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_5);
x_33 = l_Array_back___rarg(x_5, x_6);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_5);
x_37 = lean_array_get_size(x_6);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
x_40 = lean_nat_dec_lt(x_39, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_array_fget(x_6, x_39);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_6, x_39, x_42);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_nat_add(x_3, x_38);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_47, x_45);
lean_dec(x_47);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_41, 0, x_4);
x_49 = lean_array_fset(x_43, x_39, x_41);
lean_dec(x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_nat_add(x_3, x_38);
x_52 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_51, x_50);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_fset(x_43, x_39, x_53);
lean_dec(x_39);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_array_get_size(x_6);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_55, x_56);
lean_dec(x_55);
x_58 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_34);
lean_dec(x_5);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_3, x_59);
x_61 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_push(x_6, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_12);
lean_dec(x_5);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_3, x_64);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Array_insertAt___rarg(x_6, x_9, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_3, x_69);
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_6, x_72);
return x_73;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_2 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpTheoremEntry___spec__10(x_6, x_2);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_1, x_3);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
x_15 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13(x_1, x_2, x_3, x_11, x_14, x_7, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 1, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpTheoremEntry___spec__10(x_16, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_1, x_3);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3;
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
x_26 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13(x_1, x_2, x_3, x_22, x_25, x_17, x_24);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree.insertCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key sequence");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(353u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_9);
lean_dec(x_2);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(x_1, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_2, x_3, x_13, x_12);
lean_dec(x_2);
x_15 = l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(x_1, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4;
x_17 = l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_5, x_7, x_2);
x_9 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_6);
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_10, x_16, x_2);
x_18 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_12);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_inc(x_2);
x_24 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_21, x_23, x_2);
x_25 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_22);
lean_ctor_set(x_1, 2, x_25);
lean_ctor_set(x_1, 1, x_24);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_inc(x_2);
x_33 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_27, x_32, x_2);
x_34 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_28);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_31);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpTheoremEntry___spec__12(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_addSimpTheoremEntry___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_box(0);
x_6 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_4, x_2, x_5);
lean_ctor_set(x_1, 3, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_10, x_2, x_13);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 5);
x_6 = l_Std_PersistentHashMap_insert___at_Lean_Meta_getEqnsFor_x3f___spec__4(x_5, x_2, x_3);
lean_ctor_set(x_1, 5, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = l_Std_PersistentHashMap_insert___at_Lean_Meta_getEqnsFor_x3f___spec__4(x_12, x_2, x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_SimpTheorems_eraseCore(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_4, x_2);
x_9 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_5, x_2);
x_10 = lean_box(0);
lean_inc(x_2);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_6, x_2, x_10);
lean_inc(x_7);
lean_ctor_set(x_1, 4, x_11);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 2, x_8);
x_12 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_7, x_2);
if (lean_obj_tag(x_12) == 0)
{
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
return x_1;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
return x_1;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_13, x_18, x_19, x_1);
lean_dec(x_13);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_1, 4);
x_26 = lean_ctor_get(x_1, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_27 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_23, x_2);
x_28 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_24, x_2);
x_29 = lean_box(0);
lean_inc(x_2);
x_30 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_25, x_2, x_29);
lean_inc(x_26);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_26);
x_32 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_26, x_2);
if (lean_obj_tag(x_32) == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
return x_31;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
return x_31;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_33, x_38, x_39, x_31);
lean_dec(x_33);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_SimpTheorems_eraseCore(x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have [simp] attribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Meta_SimpTheorems_isLemma(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 5);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_4);
x_9 = l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_1, x_2, x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_22, x_5);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_apply_2(x_26, lean_box(0), x_27);
x_29 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_28, x_5);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
x_35 = lean_apply_4(x_30, lean_box(0), lean_box(0), x_34, x_5);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_dec(x_1);
x_10 = lean_expr_instantiate1(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
default: 
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_14, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_1 = x_15;
x_2 = x_17;
x_7 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
default: 
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_37);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_37, x_39, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_49, 0, x_38);
lean_closure_set(x_49, 1, x_40);
x_50 = 0;
x_51 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_36, x_50, x_37, x_49, x_3, x_4, x_5, x_6, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 10:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_2 = x_56;
goto _start;
}
default: 
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_7);
return x_60;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_62);
x_66 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_62, x_64, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec(x_67);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_74, 0, x_63);
lean_closure_set(x_74, 1, x_65);
x_75 = 0;
x_76 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_61, x_75, x_62, x_74, x_3, x_4, x_5, x_6, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_66);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_2 = x_81;
goto _start;
}
default: 
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_7);
return x_85;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 3);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 3);
lean_inc(x_92);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_87);
x_93 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_87, x_90, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_93, 0);
lean_dec(x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_88);
x_101 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_88, x_91, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_101, 0);
lean_dec(x_105);
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_102);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_109, 0, x_89);
lean_closure_set(x_109, 1, x_92);
x_110 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_86, x_87, x_88, x_109, x_3, x_4, x_5, x_6, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_101);
if (x_111 == 0)
{
return x_101;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_101);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_93);
if (x_115 == 0)
{
return x_93;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_93, 0);
x_117 = lean_ctor_get(x_93, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_93);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
case 10:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_2 = x_119;
goto _start;
}
default: 
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
return x_123;
}
}
}
case 10:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
lean_dec(x_1);
x_1 = x_124;
goto _start;
}
case 11:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_dec(x_2);
x_2 = x_126;
goto _start;
}
case 11:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_2, 2);
lean_inc(x_131);
lean_dec(x_2);
x_132 = lean_nat_dec_eq(x_128, x_130);
lean_dec(x_130);
lean_dec(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_box(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_7);
return x_134;
}
else
{
x_1 = x_129;
x_2 = x_131;
goto _start;
}
}
default: 
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_7);
return x_138;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_dec(x_2);
x_2 = x_139;
goto _start;
}
else
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_7);
return x_143;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `simp` theorem, equation is equivalent to");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_DiscrTree_whnfDT(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_expr_eqv(x_11, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isFVar(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; 
lean_free_object(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_mkEq(x_11, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_indentExpr(x_18);
x_21 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_24, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_expr_eqv(x_30, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Expr_isFVar(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lean_Meta_mkEq(x_30, x_2, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_indentExpr(x_39);
x_42 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_45, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_2, x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_2);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_2);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_15, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = 0;
x_17 = 1;
x_18 = 1;
lean_inc(x_1);
x_19 = l_Lean_Meta_mkLambdaFVars(x_1, x_14, x_16, x_17, x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = l_Lean_Meta_mkForallFVars(x_1, x_15, x_16, x_17, x_18, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_20);
x_25 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_2, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_free_object(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_free_object(x_11);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_11);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = 0;
x_47 = 1;
x_48 = 1;
lean_inc(x_1);
x_49 = l_Lean_Meta_mkLambdaFVars(x_1, x_44, x_46, x_47, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_Meta_mkForallFVars(x_1, x_45, x_46, x_47, x_48, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_1, x_43, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_57);
lean_ctor_set(x_2, 0, x_55);
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
lean_free_object(x_2);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_50);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_67 = x_52;
} else {
 lean_dec_ref(x_52);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_45);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_1);
x_69 = lean_ctor_get(x_49, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_49, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_71 = x_49;
} else {
 lean_dec_ref(x_49);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = 0;
x_79 = 1;
x_80 = 1;
lean_inc(x_1);
x_81 = l_Lean_Meta_mkLambdaFVars(x_1, x_75, x_78, x_79, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_1);
x_84 = l_Lean_Meta_mkForallFVars(x_1, x_76, x_78, x_79, x_80, x_3, x_4, x_5, x_6, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
if (lean_is_scalar(x_77)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_77;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_1, x_74, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_89);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_87);
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_1);
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_100 = x_84;
} else {
 lean_dec_ref(x_84);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_1);
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_104 = x_81;
} else {
 lean_dec_ref(x_81);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("True");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_mkEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEqTrue(x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("False");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_mkEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEqFalse(x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("of_not_eq_false");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("of_not_eq_true");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_10);
lean_dec(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_21, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_24 = lean_array_push(x_23, x_2);
x_25 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_mkAppM(x_25, x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10;
x_31 = l_Lean_Meta_mkEq(x_15, x_30, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
return x_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_16);
lean_dec(x_1);
x_49 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_50 = lean_array_push(x_49, x_2);
x_51 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_mkAppM(x_51, x_50, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13;
x_57 = l_Lean_Meta_mkEq(x_15, x_56, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_53);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_52);
if (x_71 == 0)
{
return x_52;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_52, 0);
x_73 = lean_ctor_get(x_52, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_52);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_mkEq(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_mkEq(x_11, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkEqFalse(x_3, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
x_11 = l_Lean_Expr_isConstOf(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
x_13 = l_Lean_Expr_isConstOf(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_17 = lean_array_push(x_16, x_3);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_mkAppM(x_18, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10;
x_24 = l_Lean_Meta_mkEq(x_1, x_23, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_42 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_43 = lean_array_push(x_42, x_3);
x_44 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_mkAppM(x_44, x_43, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13;
x_50 = l_Lean_Meta_mkEq(x_1, x_49, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_46);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_mkEq(x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkPropExt(x_4, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_34 = l_Lean_Meta_mkEq(x_3, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Meta_mkPropExt(x_4, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_mkEqSymm(x_38, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_35);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_34);
if (x_60 == 0)
{
return x_34;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_mkEq(x_4, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkEqSymm(x_2, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_17);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
x_11 = l_Lean_mkAppN(x_1, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_4, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Iff");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Ne");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid '←' modifier in rewrite rule to 'True'");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid '←' modifier in rewrite rule to 'False'");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_whnf(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_11, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Expr_isAppOfArity(x_11, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
x_21 = l_Lean_Expr_isAppOfArity(x_11, x_20, x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Expr_isAppOfArity(x_11, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
x_26 = l_Lean_Expr_isAppOfArity(x_11, x_25, x_18);
if (x_26 == 0)
{
if (x_1 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(x_11, x_3, x_27, x_5, x_6, x_7, x_8, x_12);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_3);
x_29 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
x_30 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_29, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_Lean_Expr_appFn_x21(x_11);
x_36 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_38 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_39 = l_Lean_mkProj(x_25, x_38, x_3);
x_40 = l_Lean_mkProj(x_25, x_23, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_39, x_36, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_40, x_37, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l_List_appendTR___rarg(x_42, x_46);
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
x_50 = l_List_appendTR___rarg(x_42, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_42);
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
else
{
uint8_t x_56; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
return x_41;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(x_60, x_3, x_14, x_61, x_5, x_6, x_7, x_8, x_12);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
lean_dec(x_3);
x_63 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
x_64 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_63, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Lean_Expr_appFn_x21(x_11);
x_70 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_71 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(x_70, x_71, x_3, x_72, x_5, x_6, x_7, x_8, x_12);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_3);
x_74 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
x_75 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_74, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = l_Lean_Expr_appFn_x21(x_11);
x_81 = l_Lean_Expr_appArg_x21(x_80);
lean_dec(x_80);
x_82 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_2 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_box(0);
x_84 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_1, x_81, x_82, x_3, x_83, x_5, x_6, x_7, x_8, x_12);
return x_84;
}
else
{
lean_object* x_85; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_82);
lean_inc(x_81);
x_85 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_81, x_82, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_1, x_81, x_82, x_3, x_86, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_86);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = l_Lean_Expr_appFn_x21(x_11);
x_94 = l_Lean_Expr_appArg_x21(x_93);
lean_dec(x_93);
x_95 = l_Lean_Expr_appArg_x21(x_11);
if (x_2 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_box(0);
x_97 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_1, x_3, x_11, x_95, x_94, x_96, x_5, x_6, x_7, x_8, x_12);
return x_97;
}
else
{
lean_object* x_98; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_95);
lean_inc(x_94);
x_98 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_94, x_95, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_1, x_3, x_11, x_95, x_94, x_99, x_5, x_6, x_7, x_8, x_100);
lean_dec(x_99);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_box(x_1);
x_107 = lean_box(x_2);
x_108 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed), 10, 3);
lean_closure_set(x_108, 0, x_3);
lean_closure_set(x_108, 1, x_106);
lean_closure_set(x_108, 2, x_107);
x_109 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_11, x_108, x_5, x_6, x_7, x_8, x_12);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_10);
if (x_110 == 0)
{
return x_10;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_10, 0);
x_112 = lean_ctor_get(x_10, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_10);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'simp', proposition expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_indentExpr(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_4);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of 'simp' theorem");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 5);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_20 = 2;
lean_ctor_set_uint8(x_13, 5, x_20);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
x_22 = 1;
x_23 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_22, x_2, x_23, x_21, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = l_Lean_Meta_whnfR(x_29, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
x_35 = lean_unsigned_to_nat(3u);
x_36 = l_Lean_Expr_isAppOfArity(x_32, x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_26);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = l_Lean_indentExpr(x_32);
x_38 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_41, x_8, x_9, x_10, x_11, x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Expr_appFn_x21(x_32);
x_48 = l_Lean_Expr_appArg_x21(x_47);
lean_dec(x_47);
x_49 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_48);
x_50 = l_Lean_Meta_DiscrTree_mkPath(x_48, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_48, x_49, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_ctor_set(x_26, 1, x_54);
lean_ctor_set(x_26, 0, x_51);
x_56 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_26, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_26);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_free_object(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
return x_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_31);
if (x_65 == 0)
{
return x_31;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_31, 0);
x_67 = lean_ctor_get(x_31, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_31);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_26, 1);
lean_inc(x_69);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_70 = l_Lean_Meta_whnfR(x_69, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
x_74 = lean_unsigned_to_nat(3u);
x_75 = l_Lean_Expr_isAppOfArity(x_71, x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = l_Lean_indentExpr(x_71);
x_77 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_80, x_8, x_9, x_10, x_11, x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = l_Lean_Expr_appFn_x21(x_71);
x_87 = l_Lean_Expr_appArg_x21(x_86);
lean_dec(x_86);
x_88 = l_Lean_Expr_appArg_x21(x_71);
lean_dec(x_71);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_87);
x_89 = l_Lean_Meta_DiscrTree_mkPath(x_87, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_92 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_87, x_88, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_93);
x_96 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_95, x_8, x_9, x_10, x_11, x_94);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
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
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = lean_ctor_get(x_89, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_103 = x_89;
} else {
 lean_dec_ref(x_89);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_70, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_70, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_107 = x_70;
} else {
 lean_dec_ref(x_70);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_24);
if (x_109 == 0)
{
return x_24;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_24, 0);
x_111 = lean_ctor_get(x_24, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_24);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; 
x_113 = lean_ctor_get_uint8(x_13, 0);
x_114 = lean_ctor_get_uint8(x_13, 1);
x_115 = lean_ctor_get_uint8(x_13, 2);
x_116 = lean_ctor_get_uint8(x_13, 3);
x_117 = lean_ctor_get_uint8(x_13, 4);
x_118 = lean_ctor_get_uint8(x_13, 6);
x_119 = lean_ctor_get_uint8(x_13, 7);
x_120 = lean_ctor_get_uint8(x_13, 8);
x_121 = lean_ctor_get_uint8(x_13, 9);
x_122 = lean_ctor_get_uint8(x_13, 10);
x_123 = lean_ctor_get_uint8(x_13, 11);
x_124 = lean_ctor_get_uint8(x_13, 12);
x_125 = lean_ctor_get_uint8(x_13, 13);
lean_dec(x_13);
x_126 = 2;
x_127 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_127, 0, x_113);
lean_ctor_set_uint8(x_127, 1, x_114);
lean_ctor_set_uint8(x_127, 2, x_115);
lean_ctor_set_uint8(x_127, 3, x_116);
lean_ctor_set_uint8(x_127, 4, x_117);
lean_ctor_set_uint8(x_127, 5, x_126);
lean_ctor_set_uint8(x_127, 6, x_118);
lean_ctor_set_uint8(x_127, 7, x_119);
lean_ctor_set_uint8(x_127, 8, x_120);
lean_ctor_set_uint8(x_127, 9, x_121);
lean_ctor_set_uint8(x_127, 10, x_122);
lean_ctor_set_uint8(x_127, 11, x_123);
lean_ctor_set_uint8(x_127, 12, x_124);
lean_ctor_set_uint8(x_127, 13, x_125);
x_128 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_14);
lean_ctor_set(x_128, 2, x_15);
lean_ctor_set(x_128, 3, x_16);
lean_ctor_set(x_128, 4, x_17);
lean_ctor_set(x_128, 5, x_18);
x_129 = 1;
x_130 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_131 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_129, x_2, x_130, x_128, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_137 = l_Lean_Meta_whnfR(x_135, x_8, x_9, x_10, x_11, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2;
x_141 = lean_unsigned_to_nat(3u);
x_142 = l_Lean_Expr_isAppOfArity(x_138, x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_136);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = l_Lean_indentExpr(x_138);
x_144 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_147, x_8, x_9, x_10, x_11, x_139);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = l_Lean_Expr_appFn_x21(x_138);
x_154 = l_Lean_Expr_appArg_x21(x_153);
lean_dec(x_153);
x_155 = l_Lean_Expr_appArg_x21(x_138);
lean_dec(x_138);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_154);
x_156 = l_Lean_Meta_DiscrTree_mkPath(x_154, x_8, x_9, x_10, x_11, x_139);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_159 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_154, x_155, x_8, x_9, x_10, x_11, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
if (lean_is_scalar(x_136)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_136;
}
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_160);
x_163 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_162, x_8, x_9, x_10, x_11, x_161);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_157);
lean_dec(x_136);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_159, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_159, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_166 = x_159;
} else {
 lean_dec_ref(x_159);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_136);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = lean_ctor_get(x_156, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_170 = x_156;
} else {
 lean_dec_ref(x_156);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_136);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = lean_ctor_get(x_137, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_137, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_174 = x_137;
} else {
 lean_dec_ref(x_137);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_ctor_get(x_131, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_131, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_178 = x_131;
} else {
 lean_dec_ref(x_131);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
x_15 = l_Lean_Meta_instantiateMVars(x_13, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_box(x_4);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed), 12, 7);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_6);
x_21 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_20, x_7, x_8, x_9, x_10, x_17);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_4);
x_19 = l_Lean_Meta_mkAuxLemma(x_4, x_18, x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_20);
x_22 = l_Lean_mkConst(x_20, x_6);
lean_inc(x_5);
x_23 = l_Lean_mkConst(x_20, x_5);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_22, x_25, x_23, x_2, x_3, x_24, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_8, x_27);
x_7 = x_16;
x_8 = x_29;
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_mkConst(x_1, x_15);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 2;
lean_ctor_set_uint8(x_18, 5, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_21 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_24 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_22, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_27 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_22, x_26, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
if (x_3 == 0)
{
uint8_t x_50; 
x_50 = lean_unbox(x_28);
lean_dec(x_28);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_51 = l_Lean_mkConst(x_1, x_14);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_1);
x_53 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_54 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_16, x_53, x_51, x_2, x_4, x_52, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_58 = lean_array_push(x_57, x_56);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_62 = lean_array_push(x_61, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
x_68 = lean_box(0);
x_30 = x_68;
goto block_49;
}
}
else
{
lean_object* x_69; 
lean_dec(x_28);
x_69 = lean_box(0);
x_30 = x_69;
goto block_49;
}
block_49:
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_30);
x_31 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_31, x_16, x_22, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_36 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_33, x_35, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
return x_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_24);
if (x_74 == 0)
{
return x_24;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_24, 0);
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_24);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_82 = lean_ctor_get_uint8(x_18, 0);
x_83 = lean_ctor_get_uint8(x_18, 1);
x_84 = lean_ctor_get_uint8(x_18, 2);
x_85 = lean_ctor_get_uint8(x_18, 3);
x_86 = lean_ctor_get_uint8(x_18, 4);
x_87 = lean_ctor_get_uint8(x_18, 6);
x_88 = lean_ctor_get_uint8(x_18, 7);
x_89 = lean_ctor_get_uint8(x_18, 8);
x_90 = lean_ctor_get_uint8(x_18, 9);
x_91 = lean_ctor_get_uint8(x_18, 10);
x_92 = lean_ctor_get_uint8(x_18, 11);
x_93 = lean_ctor_get_uint8(x_18, 12);
x_94 = lean_ctor_get_uint8(x_18, 13);
lean_dec(x_18);
x_95 = 2;
x_96 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_96, 0, x_82);
lean_ctor_set_uint8(x_96, 1, x_83);
lean_ctor_set_uint8(x_96, 2, x_84);
lean_ctor_set_uint8(x_96, 3, x_85);
lean_ctor_set_uint8(x_96, 4, x_86);
lean_ctor_set_uint8(x_96, 5, x_95);
lean_ctor_set_uint8(x_96, 6, x_87);
lean_ctor_set_uint8(x_96, 7, x_88);
lean_ctor_set_uint8(x_96, 8, x_89);
lean_ctor_set_uint8(x_96, 9, x_90);
lean_ctor_set_uint8(x_96, 10, x_91);
lean_ctor_set_uint8(x_96, 11, x_92);
lean_ctor_set_uint8(x_96, 12, x_93);
lean_ctor_set_uint8(x_96, 13, x_94);
lean_ctor_set(x_5, 0, x_96);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_97 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_100 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_98, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_103 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_98, x_102, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
if (x_3 == 0)
{
uint8_t x_126; 
x_126 = lean_unbox(x_104);
lean_dec(x_104);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_98);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_127 = l_Lean_mkConst(x_1, x_14);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_1);
x_129 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_130 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_16, x_129, x_127, x_2, x_4, x_128, x_5, x_6, x_7, x_8, x_105);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_135 = lean_array_push(x_134, x_131);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_130, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_139 = x_130;
} else {
 lean_dec_ref(x_130);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; 
x_141 = lean_box(0);
x_106 = x_141;
goto block_125;
}
}
else
{
lean_object* x_142; 
lean_dec(x_104);
x_142 = lean_box(0);
x_106 = x_142;
goto block_125;
}
block_125:
{
uint8_t x_107; lean_object* x_108; 
lean_dec(x_106);
x_107 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_108 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_107, x_16, x_98, x_5, x_6, x_7, x_8, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_112 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_109, x_111, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_108, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_108, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_123 = x_108;
} else {
 lean_dec_ref(x_108);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_143 = lean_ctor_get(x_103, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_103, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_145 = x_103;
} else {
 lean_dec_ref(x_103);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_147 = lean_ctor_get(x_100, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_100, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_149 = x_100;
} else {
 lean_dec_ref(x_100);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_151 = lean_ctor_get(x_97, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_97, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_153 = x_97;
} else {
 lean_dec_ref(x_97);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_155 = lean_ctor_get(x_5, 0);
x_156 = lean_ctor_get(x_5, 1);
x_157 = lean_ctor_get(x_5, 2);
x_158 = lean_ctor_get(x_5, 3);
x_159 = lean_ctor_get(x_5, 4);
x_160 = lean_ctor_get(x_5, 5);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_5);
x_161 = lean_ctor_get_uint8(x_155, 0);
x_162 = lean_ctor_get_uint8(x_155, 1);
x_163 = lean_ctor_get_uint8(x_155, 2);
x_164 = lean_ctor_get_uint8(x_155, 3);
x_165 = lean_ctor_get_uint8(x_155, 4);
x_166 = lean_ctor_get_uint8(x_155, 6);
x_167 = lean_ctor_get_uint8(x_155, 7);
x_168 = lean_ctor_get_uint8(x_155, 8);
x_169 = lean_ctor_get_uint8(x_155, 9);
x_170 = lean_ctor_get_uint8(x_155, 10);
x_171 = lean_ctor_get_uint8(x_155, 11);
x_172 = lean_ctor_get_uint8(x_155, 12);
x_173 = lean_ctor_get_uint8(x_155, 13);
if (lean_is_exclusive(x_155)) {
 x_174 = x_155;
} else {
 lean_dec_ref(x_155);
 x_174 = lean_box(0);
}
x_175 = 2;
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 0, 14);
} else {
 x_176 = x_174;
}
lean_ctor_set_uint8(x_176, 0, x_161);
lean_ctor_set_uint8(x_176, 1, x_162);
lean_ctor_set_uint8(x_176, 2, x_163);
lean_ctor_set_uint8(x_176, 3, x_164);
lean_ctor_set_uint8(x_176, 4, x_165);
lean_ctor_set_uint8(x_176, 5, x_175);
lean_ctor_set_uint8(x_176, 6, x_166);
lean_ctor_set_uint8(x_176, 7, x_167);
lean_ctor_set_uint8(x_176, 8, x_168);
lean_ctor_set_uint8(x_176, 9, x_169);
lean_ctor_set_uint8(x_176, 10, x_170);
lean_ctor_set_uint8(x_176, 11, x_171);
lean_ctor_set_uint8(x_176, 12, x_172);
lean_ctor_set_uint8(x_176, 13, x_173);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_156);
lean_ctor_set(x_177, 2, x_157);
lean_ctor_set(x_177, 3, x_158);
lean_ctor_set(x_177, 4, x_159);
lean_ctor_set(x_177, 5, x_160);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_177);
lean_inc(x_16);
x_178 = lean_infer_type(x_16, x_177, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_177);
lean_inc(x_179);
x_181 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_179, x_177, x_6, x_7, x_8, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_177);
lean_inc(x_179);
x_184 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_179, x_183, x_177, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
if (x_3 == 0)
{
uint8_t x_207; 
x_207 = lean_unbox(x_185);
lean_dec(x_185);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_179);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_208 = l_Lean_mkConst(x_1, x_14);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_1);
x_210 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_211 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_16, x_210, x_208, x_2, x_4, x_209, x_177, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_216 = lean_array_push(x_215, x_212);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_211, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_220 = x_211;
} else {
 lean_dec_ref(x_211);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; 
x_222 = lean_box(0);
x_187 = x_222;
goto block_206;
}
}
else
{
lean_object* x_223; 
lean_dec(x_185);
x_223 = lean_box(0);
x_187 = x_223;
goto block_206;
}
block_206:
{
uint8_t x_188; lean_object* x_189; 
lean_dec(x_187);
x_188 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_177);
x_189 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_188, x_16, x_179, x_177, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_193 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_190, x_192, x_177, x_6, x_7, x_8, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_200 = x_193;
} else {
 lean_dec_ref(x_193);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_177);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_202 = lean_ctor_get(x_189, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_189, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_204 = x_189;
} else {
 lean_dec_ref(x_189);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_224 = lean_ctor_get(x_184, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_184, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_226 = x_184;
} else {
 lean_dec_ref(x_184);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_228 = lean_ctor_get(x_181, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_181, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_230 = x_181;
} else {
 lean_dec_ref(x_181);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_177);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_232 = lean_ctor_get(x_178, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_178, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_234 = x_178;
} else {
 lean_dec_ref(x_178);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_10);
if (x_236 == 0)
{
return x_10;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_10, 0);
x_238 = lean_ctor_get(x_10, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_10);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_instInhabitedSimpTheorems;
x_10 = l_Lean_ScopedEnvExtension_getState___rarg(x_9, x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_instInhabitedSimpTheorems;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_14, x_1, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_13, x_2);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_ctor_set(x_10, 4, x_16);
lean_ctor_set(x_10, 0, x_15);
x_17 = lean_st_ref_set(x_7, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_7, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_5, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_23);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
x_46 = lean_ctor_get(x_10, 2);
x_47 = lean_ctor_get(x_10, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_48 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_44, x_2);
x_49 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_46);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_7, x_50, x_11);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_7, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_5, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
x_62 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 4, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
x_64 = lean_st_ref_set(x_5, x_63, x_57);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
case 1:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_6);
x_69 = lean_st_ref_take(x_7, x_8);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 4);
lean_dec(x_74);
x_75 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_73, x_2);
x_76 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_ctor_set(x_70, 4, x_76);
lean_ctor_set(x_70, 0, x_75);
x_77 = lean_st_ref_set(x_7, x_70, x_71);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_get(x_7, x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_take(x_5, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_82, 1);
lean_dec(x_85);
x_86 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
lean_ctor_set(x_82, 1, x_86);
x_87 = lean_st_ref_set(x_5, x_82, x_83);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_82, 0);
x_95 = lean_ctor_get(x_82, 2);
x_96 = lean_ctor_get(x_82, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_82);
x_97 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
x_98 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_96);
x_99 = lean_st_ref_set(x_5, x_98, x_83);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_104 = lean_ctor_get(x_70, 0);
x_105 = lean_ctor_get(x_70, 1);
x_106 = lean_ctor_get(x_70, 2);
x_107 = lean_ctor_get(x_70, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_70);
x_108 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_104, x_2);
x_109 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_105);
lean_ctor_set(x_110, 2, x_106);
lean_ctor_set(x_110, 3, x_107);
lean_ctor_set(x_110, 4, x_109);
x_111 = lean_st_ref_set(x_7, x_110, x_71);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_st_ref_get(x_7, x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_take(x_5, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 3);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
x_122 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 4, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_119);
lean_ctor_set(x_123, 3, x_120);
x_124 = lean_st_ref_set(x_5, x_123, x_117);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_6, 4);
lean_inc(x_129);
lean_dec(x_6);
x_130 = lean_st_ref_take(x_7, x_8);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_134 = lean_ctor_get(x_131, 0);
x_135 = lean_ctor_get(x_131, 4);
lean_dec(x_135);
x_136 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_134, x_129, x_2);
x_137 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_ctor_set(x_131, 4, x_137);
lean_ctor_set(x_131, 0, x_136);
x_138 = lean_st_ref_set(x_7, x_131, x_132);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_st_ref_get(x_7, x_139);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_5, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_143, 1);
lean_dec(x_146);
x_147 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
lean_ctor_set(x_143, 1, x_147);
x_148 = lean_st_ref_set(x_5, x_143, x_144);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
x_151 = lean_box(0);
lean_ctor_set(x_148, 0, x_151);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_155 = lean_ctor_get(x_143, 0);
x_156 = lean_ctor_get(x_143, 2);
x_157 = lean_ctor_get(x_143, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_143);
x_158 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
x_159 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_157);
x_160 = lean_st_ref_set(x_5, x_159, x_144);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_165 = lean_ctor_get(x_131, 0);
x_166 = lean_ctor_get(x_131, 1);
x_167 = lean_ctor_get(x_131, 2);
x_168 = lean_ctor_get(x_131, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_131);
x_169 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_165, x_129, x_2);
x_170 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
x_171 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_166);
lean_ctor_set(x_171, 2, x_167);
lean_ctor_set(x_171, 3, x_168);
lean_ctor_set(x_171, 4, x_170);
x_172 = lean_st_ref_set(x_7, x_171, x_132);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_st_ref_get(x_7, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_take(x_5, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 3);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
x_183 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 4, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_180);
lean_ctor_set(x_184, 3, x_181);
x_185 = lean_st_ref_set(x_5, x_184, x_178);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_9);
lean_inc(x_1);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_15, x_2, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_20 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
x_11 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(x_1, x_5, x_13, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_addSimpTheorem(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Meta_addSimpTheorem(x_1, x_16, x_3, x_17, x_2, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_22 = lean_box(0);
x_7 = x_21;
x_8 = x_22;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_SimpTheorems_erase___rarg___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__3(x_14, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(x_1, x_2, x_20, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(x_1, x_2, x_22, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(x_1, x_2, x_24, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_1);
lean_ctor_set_uint8(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, 5, x_2);
lean_ctor_set_uint8(x_4, 6, x_3);
lean_ctor_set_uint8(x_4, 7, x_1);
lean_ctor_set_uint8(x_4, 8, x_3);
lean_ctor_set_uint8(x_4, 9, x_3);
lean_ctor_set_uint8(x_4, 10, x_1);
lean_ctor_set_uint8(x_4, 11, x_3);
lean_ctor_set_uint8(x_4, 12, x_3);
lean_ctor_set_uint8(x_4, 13, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
x_4 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
x_3 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'simp', it is not a proposition nor a definition (to unfold)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__14;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__16;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simpPost");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__18;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_26; lean_object* x_27; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_26 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
lean_inc(x_2);
x_27 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_2, x_26, x_12, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_95 = lean_unsigned_to_nat(1u);
x_96 = l_Lean_Syntax_getArg(x_3, x_95);
x_97 = l_Lean_Syntax_isNone(x_96);
x_98 = lean_unsigned_to_nat(2u);
x_99 = l_Lean_Syntax_getArg(x_3, x_98);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_getAttrParamOptPrio(x_99, x_5, x_6, x_29);
if (x_97 == 0)
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unsigned_to_nat(0u);
x_104 = l_Lean_Syntax_getArg(x_96, x_103);
lean_dec(x_96);
x_105 = l_Lean_Syntax_getKind(x_104);
x_106 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__20;
x_107 = lean_name_eq(x_105, x_106);
lean_dec(x_105);
x_30 = x_107;
x_31 = x_101;
x_32 = x_102;
goto block_94;
}
else
{
uint8_t x_108; 
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
return x_100;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_dec(x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_114 = 1;
x_30 = x_114;
x_31 = x_112;
x_32 = x_113;
goto block_94;
}
else
{
uint8_t x_115; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_100);
if (x_115 == 0)
{
return x_100;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_100, 0);
x_117 = lean_ctor_get(x_100, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_100);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
block_94:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_ConstantInfo_type(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_34 = l_Lean_Meta_isProp(x_33, x_26, x_12, x_5, x_6, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_ConstantInfo_hasValue(x_28);
lean_dec(x_28);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
x_40 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_39, x_26, x_12, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_2);
x_46 = l_Lean_Meta_getEqnsFor_x3f(x_2, x_45, x_26, x_12, x_5, x_6, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_31);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_2);
x_50 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_49, x_4, x_26, x_12, x_5, x_6, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_14 = x_51;
x_15 = x_52;
goto block_25;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_array_get_size(x_54);
x_56 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_57 = 0;
x_58 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_1);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_4, x_30, x_31, x_54, x_56, x_57, x_58, x_26, x_12, x_5, x_6, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_2);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_54);
lean_inc(x_5);
lean_inc(x_1);
x_62 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_61, x_4, x_26, x_12, x_5, x_6, x_60);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_2);
x_68 = l_Lean_Meta_hasSmartUnfoldingDecl(x_67, x_2);
if (x_68 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_58;
x_15 = x_66;
goto block_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_2);
x_70 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_69, x_4, x_26, x_12, x_5, x_6, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_14 = x_71;
x_15 = x_72;
goto block_25;
}
}
else
{
uint8_t x_73; 
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_59);
if (x_73 == 0)
{
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_59, 0);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_59);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_46);
if (x_77 == 0)
{
return x_46;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_46, 0);
x_79 = lean_ctor_get(x_46, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_46);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
lean_dec(x_28);
x_81 = lean_ctor_get(x_34, 1);
lean_inc(x_81);
lean_dec(x_34);
x_82 = 0;
lean_inc(x_6);
lean_inc(x_12);
x_83 = l_Lean_Meta_addSimpTheorem(x_1, x_2, x_30, x_82, x_4, x_31, x_26, x_12, x_5, x_6, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_14 = x_84;
x_15 = x_85;
goto block_25;
}
else
{
uint8_t x_86; 
lean_dec(x_12);
lean_dec(x_6);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_34);
if (x_90 == 0)
{
return x_34;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_34, 0);
x_92 = lean_ctor_get(x_34, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_34);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_27);
if (x_119 == 0)
{
return x_27;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_27, 0);
x_121 = lean_ctor_get(x_27, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_27);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
block_25:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_16 = lean_st_ref_get(x_6, x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_12, x_17);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_instInhabitedSimpTheorems;
x_11 = l_Lean_ScopedEnvExtension_getState___rarg(x_10, x_1, x_9);
lean_dec(x_9);
lean_inc(x_4);
x_12 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2(x_11, x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 4);
lean_dec(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__2___boxed), 2, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_1, x_19, x_21);
x_23 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 0, x_22);
x_24 = lean_st_ref_set(x_4, x_16, x_17);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 2);
x_34 = lean_ctor_get(x_16, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__2___boxed), 2, 1);
lean_closure_set(x_35, 0, x_13);
x_36 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_1, x_31, x_35);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_4, x_38, x_17);
lean_dec(x_4);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 1;
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_5);
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__1___boxed), 7, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__3___boxed), 5, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_Lean_registerBuiltinAttribute(x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_14, x_15, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_mkSimpAttr___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_mkSimpAttr___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkSimpAttr___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_addSimpTheoremEntry(x_1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(x_1, x_7, x_8);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SimpTheorems_pre___default___closed__1;
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Meta_Instances_instanceNames___default___spec__1;
x_3 = l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3;
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Meta_mkSimpExt___closed__2;
x_4 = l_Lean_Meta_mkSimpExt___closed__1;
x_5 = l_Lean_Meta_mkSimpExt___closed__3;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
x_7 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_mkHashMapImp___rarg(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072____spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072____spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtensionMapRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkSimpExt(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkSimpAttr(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_registerSimpAttr___closed__1;
x_11 = lean_st_ref_take(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
x_14 = l_Std_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(x_12, x_1, x_6);
x_15 = lean_st_ref_set(x_10, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Ext");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3;
x_3 = lean_name_append_after(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simplification theorem");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_registerSimpAttr___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(x_6, x_1);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getSimpTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_getSimpTheorems___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_addSimpTheoremEntry(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 4);
x_13 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_12, x_2);
lean_ctor_set(x_1, 4, x_13);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_16, x_21, x_22, x_1);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_array_get_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_24, x_32, x_33, x_1);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get(x_1, 3);
x_44 = lean_ctor_get(x_1, 4);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_46 = l_Std_PersistentHashMap_erase___at_Lean_Meta_Instances_eraseCore___spec__1(x_44, x_2);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_45);
x_48 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_array_get_size(x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_lt(x_53, x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_49);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_52, x_52);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_49);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_49, x_58, x_59, x_47);
lean_dec(x_49);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_47);
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_64 = x_48;
} else {
 lean_dec_ref(x_48);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateConst!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SimpTheorem_getValue___closed__1;
x_2 = l_Lean_Meta_SimpTheorem_getValue___closed__2;
x_3 = lean_unsigned_to_nat(1060u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_SimpTheorem_getValue___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_9);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_11, x_12, x_9, x_2, x_3, x_4, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_9, x_15, x_7);
lean_dec(x_15);
lean_dec(x_9);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_9, x_17, x_7);
lean_dec(x_17);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Array_isEmpty___rarg(x_21);
if (x_22 == 0)
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
lean_inc(x_21);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_24, x_25, x_21, x_2, x_3, x_4, x_5, x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_21, x_28, x_7);
lean_dec(x_28);
lean_dec(x_21);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_21, x_30, x_7);
lean_dec(x_30);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_34 = l_Lean_Expr_constName_x21(x_7);
x_35 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_34, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_ConstantInfo_levelParams(x_37);
lean_dec(x_37);
x_40 = l_List_isEmpty___rarg(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_free_object(x_35);
x_41 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_39, x_2, x_3, x_4, x_5, x_38);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_expr_update_const(x_7, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_50 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set_uint64(x_50, sizeof(void*)*2, x_49);
x_51 = lean_expr_update_const(x_50, x_46);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_ctor_get(x_7, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_57 = x_7;
} else {
 lean_dec_ref(x_7);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(4, 2, 8);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set_uint64(x_58, sizeof(void*)*2, x_56);
x_59 = lean_expr_update_const(x_58, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
lean_dec(x_62);
x_63 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_64 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_63);
lean_ctor_set(x_41, 0, x_64);
return x_41;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_dec(x_41);
x_66 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_67 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
}
else
{
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_7);
return x_35;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = l_Lean_ConstantInfo_levelParams(x_69);
lean_dec(x_69);
x_72 = l_List_isEmpty___rarg(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_71, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
x_79 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_80 = x_7;
} else {
 lean_dec_ref(x_7);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(4, 2, 8);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set_uint64(x_81, sizeof(void*)*2, x_79);
x_82 = lean_expr_update_const(x_81, x_74);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_7);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_85 = x_73;
} else {
 lean_dec_ref(x_73);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_87 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
else
{
lean_object* x_89; 
lean_dec(x_71);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_7);
lean_ctor_set(x_89, 1, x_70);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_7);
x_90 = !lean_is_exclusive(x_35);
if (x_90 == 0)
{
return x_35;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_35, 0);
x_92 = lean_ctor_get(x_35, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_35);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_13, x_1, x_9, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_List_redLength___rarg(x_16);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
x_19 = l_List_toArrayAux___rarg(x_16, x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_21, x_22, x_19);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = l_List_redLength___rarg(x_24);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___rarg(x_24, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_30, x_31, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_7, x_6, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_15);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_15, x_1, x_15, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_23 = lean_array_uset(x_17, x_6, x_19);
x_6 = x_22;
x_7 = x_23;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheorems(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 2;
lean_ctor_set_uint8(x_13, 5, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_2, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(x_1, x_3, x_5, x_6, x_20, x_21, x_17, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get_uint8(x_13, 0);
x_36 = lean_ctor_get_uint8(x_13, 1);
x_37 = lean_ctor_get_uint8(x_13, 2);
x_38 = lean_ctor_get_uint8(x_13, 3);
x_39 = lean_ctor_get_uint8(x_13, 4);
x_40 = lean_ctor_get_uint8(x_13, 6);
x_41 = lean_ctor_get_uint8(x_13, 7);
x_42 = lean_ctor_get_uint8(x_13, 8);
x_43 = lean_ctor_get_uint8(x_13, 9);
x_44 = lean_ctor_get_uint8(x_13, 10);
x_45 = lean_ctor_get_uint8(x_13, 11);
x_46 = lean_ctor_get_uint8(x_13, 12);
x_47 = lean_ctor_get_uint8(x_13, 13);
lean_dec(x_13);
x_48 = 2;
x_49 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_49, 0, x_35);
lean_ctor_set_uint8(x_49, 1, x_36);
lean_ctor_set_uint8(x_49, 2, x_37);
lean_ctor_set_uint8(x_49, 3, x_38);
lean_ctor_set_uint8(x_49, 4, x_39);
lean_ctor_set_uint8(x_49, 5, x_48);
lean_ctor_set_uint8(x_49, 6, x_40);
lean_ctor_set_uint8(x_49, 7, x_41);
lean_ctor_set_uint8(x_49, 8, x_42);
lean_ctor_set_uint8(x_49, 9, x_43);
lean_ctor_set_uint8(x_49, 10, x_44);
lean_ctor_set_uint8(x_49, 11, x_45);
lean_ctor_set_uint8(x_49, 12, x_46);
lean_ctor_set_uint8(x_49, 13, x_47);
lean_ctor_set(x_7, 0, x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_50 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_2, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_get_size(x_51);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = 0;
x_56 = l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(x_1, x_3, x_5, x_6, x_54, x_55, x_51, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_65 = lean_ctor_get(x_50, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_67 = x_50;
} else {
 lean_dec_ref(x_50);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_69 = lean_ctor_get(x_7, 0);
x_70 = lean_ctor_get(x_7, 1);
x_71 = lean_ctor_get(x_7, 2);
x_72 = lean_ctor_get(x_7, 3);
x_73 = lean_ctor_get(x_7, 4);
x_74 = lean_ctor_get(x_7, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_7);
x_75 = lean_ctor_get_uint8(x_69, 0);
x_76 = lean_ctor_get_uint8(x_69, 1);
x_77 = lean_ctor_get_uint8(x_69, 2);
x_78 = lean_ctor_get_uint8(x_69, 3);
x_79 = lean_ctor_get_uint8(x_69, 4);
x_80 = lean_ctor_get_uint8(x_69, 6);
x_81 = lean_ctor_get_uint8(x_69, 7);
x_82 = lean_ctor_get_uint8(x_69, 8);
x_83 = lean_ctor_get_uint8(x_69, 9);
x_84 = lean_ctor_get_uint8(x_69, 10);
x_85 = lean_ctor_get_uint8(x_69, 11);
x_86 = lean_ctor_get_uint8(x_69, 12);
x_87 = lean_ctor_get_uint8(x_69, 13);
if (lean_is_exclusive(x_69)) {
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
x_89 = 2;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 0, 14);
} else {
 x_90 = x_88;
}
lean_ctor_set_uint8(x_90, 0, x_75);
lean_ctor_set_uint8(x_90, 1, x_76);
lean_ctor_set_uint8(x_90, 2, x_77);
lean_ctor_set_uint8(x_90, 3, x_78);
lean_ctor_set_uint8(x_90, 4, x_79);
lean_ctor_set_uint8(x_90, 5, x_89);
lean_ctor_set_uint8(x_90, 6, x_80);
lean_ctor_set_uint8(x_90, 7, x_81);
lean_ctor_set_uint8(x_90, 8, x_82);
lean_ctor_set_uint8(x_90, 9, x_83);
lean_ctor_set_uint8(x_90, 10, x_84);
lean_ctor_set_uint8(x_90, 11, x_85);
lean_ctor_set_uint8(x_90, 12, x_86);
lean_ctor_set_uint8(x_90, 13, x_87);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_70);
lean_ctor_set(x_91, 2, x_71);
lean_ctor_set(x_91, 3, x_72);
lean_ctor_set(x_91, 4, x_73);
lean_ctor_set(x_91, 5, x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_91);
x_92 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_2, x_4, x_91, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_array_get_size(x_93);
x_96 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_97 = 0;
x_98 = l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(x_1, x_3, x_5, x_6, x_96, x_97, x_93, x_91, x_8, x_9, x_10, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_107 = lean_ctor_get(x_92, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_92, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_109 = x_92;
} else {
 lean_dec_ref(x_92);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpTheorems___spec__1(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_mkSimpTheorems(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add_getName_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_getAppFn(x_2);
x_9 = l_Lean_Expr_isConst(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isFVar(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Meta_getFVarLocalDecl(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_LocalDecl_userName(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_27 = l_Lean_Expr_constName_x21(x_8);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add_getName_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_add_getName_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isConst(x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_8);
x_14 = l_Lean_Meta_SimpTheorems_add_getName_x3f(x_7, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkSimpTheorems(x_2, x_3, x_5, x_4, x_6, x_15, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_19, x_24, x_25, x_1);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_array_get_size(x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_27, x_35, x_36, x_1);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
lean_dec(x_2);
x_47 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_48 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_47, x_5, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = 1;
x_14 = 0;
x_15 = lean_unsigned_to_nat(1000u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_SimpTheorems_addConst(x_4, x_12, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_17;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_2, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_2, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(x_18, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_6, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1;
lean_inc(x_1);
x_30 = l_Lean_Meta_hasSmartUnfoldingDecl(x_28, x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_apply_7(x_29, x_23, x_31, x_3, x_4, x_5, x_6, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_23, x_1);
x_34 = lean_box(0);
x_35 = lean_apply_7(x_29, x_33, x_34, x_3, x_4, x_5, x_6, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
x_10 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_11 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1___rarg(x_9, x_10, x_8, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_fget(x_1, x_11);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_1, x_11, x_15);
x_17 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_18 = 0;
x_19 = 1;
x_20 = lean_unsigned_to_nat(1000u);
x_21 = l_Lean_Meta_SimpTheorems_add(x_14, x_17, x_2, x_18, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_array_fset(x_16, x_11, x_23);
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
x_27 = lean_array_fset(x_16, x_11, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_33 = l_Lean_Meta_mkSimpExt___closed__1;
x_34 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_35 = 0;
x_36 = 1;
x_37 = lean_unsigned_to_nat(1000u);
x_38 = l_Lean_Meta_SimpTheorems_add(x_33, x_34, x_2, x_35, x_36, x_37, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_42 = lean_array_push(x_41, x_40);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(x_2, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_7, x_1);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(x_2, x_1, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isErased(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_6, x_1);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(x_2, x_1, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__14;
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandRegister_simp_attr___");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__2;
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("register_simp_attr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__6;
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__8;
x_3 = l_Lean_Meta_commandRegister__simp__attr_________closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__6;
x_2 = l_Lean_Meta_commandRegister__simp__attr_________closed__12;
x_3 = l_Lean_Meta_commandRegister__simp__attr_________closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr_________closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Meta_commandRegister__simp__attr_________closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_commandRegister__simp__attr______() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__17;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__16;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("initialize");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6;
x_3 = l_Lean_Meta_SimpTheorem_keys___default___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ext");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__16;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeSpec");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SimpExtension");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__2;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("←");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqIndent");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqItem");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("registerSimpAttr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_commandRegister__simp__attr_________closed__2;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotedName");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13;
x_2 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_commandRegister__simp__attr_________closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3;
lean_inc(x_14);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11;
lean_inc(x_15);
lean_inc(x_16);
x_20 = l_Lean_addMacroScope(x_16, x_19, x_15);
x_21 = lean_box(0);
x_22 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10;
lean_inc(x_14);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = l_Lean_Meta_instToFormatSimpTheorem___closed__1;
lean_inc(x_14);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19;
lean_inc(x_15);
lean_inc(x_16);
x_27 = l_Lean_addMacroScope(x_16, x_26, x_15);
x_28 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18;
x_29 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22;
lean_inc(x_14);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23;
x_32 = lean_array_push(x_31, x_25);
x_33 = lean_array_push(x_32, x_30);
x_34 = lean_box(2);
x_35 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15;
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
x_37 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24;
lean_inc(x_14);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25;
x_40 = lean_array_push(x_39, x_23);
x_41 = lean_array_push(x_40, x_36);
x_42 = lean_array_push(x_41, x_38);
x_43 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
x_45 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37;
x_46 = l_Lean_addMacroScope(x_16, x_45, x_15);
x_47 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36;
x_48 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40;
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
lean_inc(x_50);
x_51 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_21, x_50);
x_52 = lean_array_push(x_31, x_49);
x_53 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42;
x_54 = lean_array_push(x_53, x_18);
x_55 = lean_array_push(x_54, x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = l___private_Init_Meta_0__Lean_quoteNameMk(x_50);
x_57 = lean_array_push(x_31, x_56);
x_58 = lean_array_push(x_57, x_11);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_array_push(x_52, x_59);
x_61 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33;
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_34);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
x_63 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_34);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
x_67 = lean_array_push(x_31, x_66);
x_68 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
x_69 = lean_array_push(x_67, x_68);
x_70 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = lean_array_push(x_63, x_71);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_34);
lean_ctor_set(x_73, 1, x_43);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_array_push(x_63, x_73);
x_75 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27;
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_74);
x_77 = lean_array_push(x_55, x_76);
x_78 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4;
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_34);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_12, 0, x_79);
return x_12;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_50);
x_80 = lean_ctor_get(x_51, 0);
lean_inc(x_80);
lean_dec(x_51);
x_81 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45;
x_82 = l_String_intercalate(x_81, x_80);
x_83 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l_Lean_nameLitKind;
x_86 = l_Lean_Syntax_mkLit(x_85, x_84, x_34);
x_87 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44;
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_34);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
x_91 = lean_array_push(x_31, x_90);
x_92 = lean_array_push(x_91, x_11);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_34);
lean_ctor_set(x_93, 1, x_43);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_array_push(x_52, x_93);
x_95 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33;
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_34);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_94);
x_97 = lean_array_push(x_87, x_96);
x_98 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31;
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_34);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_97);
x_100 = lean_array_push(x_31, x_99);
x_101 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
x_102 = lean_array_push(x_100, x_101);
x_103 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29;
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_34);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_102);
x_105 = lean_array_push(x_87, x_104);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_34);
lean_ctor_set(x_106, 1, x_43);
lean_ctor_set(x_106, 2, x_105);
x_107 = lean_array_push(x_87, x_106);
x_108 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27;
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_107);
x_110 = lean_array_push(x_55, x_109);
x_111 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4;
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_34);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_12, 0, x_112);
return x_12;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_113 = lean_ctor_get(x_12, 0);
x_114 = lean_ctor_get(x_12, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_12);
x_115 = lean_ctor_get(x_2, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 1);
lean_inc(x_116);
lean_dec(x_2);
x_117 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3;
lean_inc(x_113);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11;
lean_inc(x_115);
lean_inc(x_116);
x_120 = l_Lean_addMacroScope(x_116, x_119, x_115);
x_121 = lean_box(0);
x_122 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10;
lean_inc(x_113);
x_123 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_120);
lean_ctor_set(x_123, 3, x_121);
x_124 = l_Lean_Meta_instToFormatSimpTheorem___closed__1;
lean_inc(x_113);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19;
lean_inc(x_115);
lean_inc(x_116);
x_127 = l_Lean_addMacroScope(x_116, x_126, x_115);
x_128 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18;
x_129 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22;
lean_inc(x_113);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_113);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_129);
x_131 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23;
x_132 = lean_array_push(x_131, x_125);
x_133 = lean_array_push(x_132, x_130);
x_134 = lean_box(2);
x_135 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15;
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_133);
x_137 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24;
lean_inc(x_113);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_113);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25;
x_140 = lean_array_push(x_139, x_123);
x_141 = lean_array_push(x_140, x_136);
x_142 = lean_array_push(x_141, x_138);
x_143 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6;
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_142);
x_145 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37;
x_146 = l_Lean_addMacroScope(x_116, x_145, x_115);
x_147 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36;
x_148 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40;
x_149 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_149, 0, x_113);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_148);
x_150 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
lean_inc(x_150);
x_151 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_121, x_150);
x_152 = lean_array_push(x_131, x_149);
x_153 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42;
x_154 = lean_array_push(x_153, x_118);
x_155 = lean_array_push(x_154, x_144);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_156 = l___private_Init_Meta_0__Lean_quoteNameMk(x_150);
x_157 = lean_array_push(x_131, x_156);
x_158 = lean_array_push(x_157, x_11);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_134);
lean_ctor_set(x_159, 1, x_143);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_array_push(x_152, x_159);
x_161 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33;
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_134);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_160);
x_163 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_164 = lean_array_push(x_163, x_162);
x_165 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31;
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_134);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_164);
x_167 = lean_array_push(x_131, x_166);
x_168 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
x_169 = lean_array_push(x_167, x_168);
x_170 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29;
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_134);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_169);
x_172 = lean_array_push(x_163, x_171);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_134);
lean_ctor_set(x_173, 1, x_143);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_array_push(x_163, x_173);
x_175 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27;
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_134);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_174);
x_177 = lean_array_push(x_155, x_176);
x_178 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4;
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_134);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_114);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_150);
x_181 = lean_ctor_get(x_151, 0);
lean_inc(x_181);
lean_dec(x_151);
x_182 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45;
x_183 = l_String_intercalate(x_182, x_181);
x_184 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46;
x_185 = lean_string_append(x_184, x_183);
lean_dec(x_183);
x_186 = l_Lean_nameLitKind;
x_187 = l_Lean_Syntax_mkLit(x_186, x_185, x_134);
x_188 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_189 = lean_array_push(x_188, x_187);
x_190 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44;
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_134);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set(x_191, 2, x_189);
x_192 = lean_array_push(x_131, x_191);
x_193 = lean_array_push(x_192, x_11);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_134);
lean_ctor_set(x_194, 1, x_143);
lean_ctor_set(x_194, 2, x_193);
x_195 = lean_array_push(x_152, x_194);
x_196 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33;
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_134);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_197, 2, x_195);
x_198 = lean_array_push(x_188, x_197);
x_199 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31;
x_200 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_200, 0, x_134);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_198);
x_201 = lean_array_push(x_131, x_200);
x_202 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7;
x_203 = lean_array_push(x_201, x_202);
x_204 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29;
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_134);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_203);
x_206 = lean_array_push(x_188, x_205);
x_207 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_207, 0, x_134);
lean_ctor_set(x_207, 1, x_143);
lean_ctor_set(x_207, 2, x_206);
x_208 = lean_array_push(x_188, x_207);
x_209 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27;
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_134);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_208);
x_211 = lean_array_push(x_155, x_210);
x_212 = l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4;
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_134);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_213, 2, x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_114);
return x_214;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SimpTheorem_keys___default___closed__1 = _init_l_Lean_Meta_SimpTheorem_keys___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_keys___default___closed__1);
l_Lean_Meta_SimpTheorem_keys___default = _init_l_Lean_Meta_SimpTheorem_keys___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_keys___default);
l_Lean_Meta_SimpTheorem_levelParams___default = _init_l_Lean_Meta_SimpTheorem_levelParams___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_levelParams___default);
l_Lean_Meta_SimpTheorem_priority___default = _init_l_Lean_Meta_SimpTheorem_priority___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_priority___default);
l_Lean_Meta_SimpTheorem_post___default = _init_l_Lean_Meta_SimpTheorem_post___default();
l_Lean_Meta_SimpTheorem_perm___default = _init_l_Lean_Meta_SimpTheorem_perm___default();
l_Lean_Meta_SimpTheorem_name_x3f___default = _init_l_Lean_Meta_SimpTheorem_name_x3f___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_name_x3f___default);
l_Lean_Meta_instInhabitedSimpTheorem___closed__1 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1();
l_Lean_Meta_instInhabitedSimpTheorem___closed__2 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__2);
l_Lean_Meta_instInhabitedSimpTheorem___closed__3 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__3);
l_Lean_Meta_instInhabitedSimpTheorem = _init_l_Lean_Meta_instInhabitedSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem);
l_Lean_Meta_SimpTheorem_getName___closed__1 = _init_l_Lean_Meta_SimpTheorem_getName___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getName___closed__1);
l_Lean_Meta_SimpTheorem_getName___closed__2 = _init_l_Lean_Meta_SimpTheorem_getName___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getName___closed__2);
l_Lean_Meta_instToFormatSimpTheorem___closed__1 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__1);
l_Lean_Meta_instToFormatSimpTheorem___closed__2 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__2);
l_Lean_Meta_instToFormatSimpTheorem___closed__3 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__3);
l_Lean_Meta_instToFormatSimpTheorem___closed__4 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__4);
l_Lean_Meta_instToFormatSimpTheorem___closed__5 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__5();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__5);
l_Lean_Meta_instToFormatSimpTheorem___closed__6 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__6();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__6);
l_Lean_Meta_SimpTheorems_pre___default___closed__1 = _init_l_Lean_Meta_SimpTheorems_pre___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_pre___default___closed__1);
l_Lean_Meta_SimpTheorems_pre___default = _init_l_Lean_Meta_SimpTheorems_pre___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_pre___default);
l_Lean_Meta_SimpTheorems_post___default = _init_l_Lean_Meta_SimpTheorems_post___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_post___default);
l_Lean_Meta_SimpTheorems_lemmaNames___default = _init_l_Lean_Meta_SimpTheorems_lemmaNames___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_lemmaNames___default);
l_Lean_Meta_SimpTheorems_toUnfold___default = _init_l_Lean_Meta_SimpTheorems_toUnfold___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_toUnfold___default);
l_Lean_Meta_SimpTheorems_erased___default = _init_l_Lean_Meta_SimpTheorems_erased___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erased___default);
l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1 = _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__1);
l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2 = _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__2);
l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3 = _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_toUnfoldThms___default___closed__3);
l_Lean_Meta_SimpTheorems_toUnfoldThms___default = _init_l_Lean_Meta_SimpTheorems_toUnfoldThms___default();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_toUnfoldThms___default);
l_Lean_Meta_instInhabitedSimpTheorems___closed__1 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__1);
l_Lean_Meta_instInhabitedSimpTheorems___closed__2 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__2);
l_Lean_Meta_instInhabitedSimpTheorems = _init_l_Lean_Meta_instInhabitedSimpTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems);
l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__3);
l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1 = _init_l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__15___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4);
l_Lean_Meta_SimpTheorems_erase___rarg___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___closed__1);
l_Lean_Meta_SimpTheorems_erase___rarg___closed__2 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___closed__2);
l_Lean_Meta_SimpTheorems_erase___rarg___closed__3 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___closed__3);
l_Lean_Meta_SimpTheorems_erase___rarg___closed__4 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__10);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__11);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__12);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__13);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2);
l_Lean_Meta_instInhabitedSimpEntry___closed__1 = _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry___closed__1);
l_Lean_Meta_instInhabitedSimpEntry = _init_l_Lean_Meta_instInhabitedSimpEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__3 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__3);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__4);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__5);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__6 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__6();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__6);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__7 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__7();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__7);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__8);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__9);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__1 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__1);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__2 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__2);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__3 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__3);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__4 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__4);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__5 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__5);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__6 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__6);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__7 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__7);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__8 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__8);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__9 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__9);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__10 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__10);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__11 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__11);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__12 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__12);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__13 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__13);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__14 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__14);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__15 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__15);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__16 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__16);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__17 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__17);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__18 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__18);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__19 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__19);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__20 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__20);
l_Lean_Meta_mkSimpExt___closed__1 = _init_l_Lean_Meta_mkSimpExt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__1);
l_Lean_Meta_mkSimpExt___closed__2 = _init_l_Lean_Meta_mkSimpExt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__2);
l_Lean_Meta_mkSimpExt___closed__3 = _init_l_Lean_Meta_mkSimpExt___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__3);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4072_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtensionMapRef);
lean_dec_ref(res);
}l_Lean_Meta_registerSimpAttr___closed__1 = _init_l_Lean_Meta_registerSimpAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_registerSimpAttr___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_4167_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
}l_Lean_Meta_getSimpTheorems___closed__1 = _init_l_Lean_Meta_getSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_getSimpTheorems___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__1 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__2 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__2);
l_Lean_Meta_SimpTheorem_getValue___closed__3 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__3);
l_Lean_Meta_SimpTheorem_getValue___closed__4 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__4);
l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1 = _init_l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__2___closed__1);
l_Lean_Meta_commandRegister__simp__attr_________closed__1 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__1();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__1);
l_Lean_Meta_commandRegister__simp__attr_________closed__2 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__2();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__2);
l_Lean_Meta_commandRegister__simp__attr_________closed__3 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__3();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__3);
l_Lean_Meta_commandRegister__simp__attr_________closed__4 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__4();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__4);
l_Lean_Meta_commandRegister__simp__attr_________closed__5 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__5();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__5);
l_Lean_Meta_commandRegister__simp__attr_________closed__6 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__6();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__6);
l_Lean_Meta_commandRegister__simp__attr_________closed__7 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__7();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__7);
l_Lean_Meta_commandRegister__simp__attr_________closed__8 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__8();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__8);
l_Lean_Meta_commandRegister__simp__attr_________closed__9 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__9();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__9);
l_Lean_Meta_commandRegister__simp__attr_________closed__10 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__10();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__10);
l_Lean_Meta_commandRegister__simp__attr_________closed__11 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__11();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__11);
l_Lean_Meta_commandRegister__simp__attr_________closed__12 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__12();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__12);
l_Lean_Meta_commandRegister__simp__attr_________closed__13 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__13();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__13);
l_Lean_Meta_commandRegister__simp__attr_________closed__14 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__14();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__14);
l_Lean_Meta_commandRegister__simp__attr_________closed__15 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__15();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__15);
l_Lean_Meta_commandRegister__simp__attr_________closed__16 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__16();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__16);
l_Lean_Meta_commandRegister__simp__attr_________closed__17 = _init_l_Lean_Meta_commandRegister__simp__attr_________closed__17();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr_________closed__17);
l_Lean_Meta_commandRegister__simp__attr______ = _init_l_Lean_Meta_commandRegister__simp__attr______();
lean_mark_persistent(l_Lean_Meta_commandRegister__simp__attr______);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__1);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__2);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__3);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__4);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__5);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__6);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__7);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__8);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__9);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__10);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__11);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__12);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__13);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__14);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__15);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__16);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__17);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__18);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__19);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__20);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__21);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__22);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__23);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__24);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__25);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__26);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__27);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__28);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__29);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__30);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__31);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__32);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__33);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__34);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__35);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__36);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__37);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__38);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__39);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__40);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__41);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__42);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__43);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__44);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__45);
l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46 = _init_l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46();
lean_mark_persistent(l_Lean_Meta___aux__Lean__Meta__Tactic__Simp__SimpTheorems______macroRules__Lean__Meta__commandRegister__simp__attr________1___closed__46);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
