// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Eqns
// Imports: Init Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Split Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns
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
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3;
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4;
lean_object* l_Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
static lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1;
static lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___boxed(lean_object*);
static lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6;
static lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4;
static lean_object* l_Lean_Elab_WF_registerEqnsInfo___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12;
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816_(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1;
lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8;
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_WF_instInhabitedEqnInfo___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2;
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1;
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6;
static lean_object* l_Lean_Elab_WF_mkEqns___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint64_t _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3;
x_2 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4;
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("deltaLHSUntilFix");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WellFounded");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fix");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
lean_dec(x_9);
x_14 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4;
x_15 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7;
x_16 = lean_box(0);
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_1, x_15, x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Expr_appFn_x21(x_9);
lean_dec(x_9);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11;
x_21 = l_Lean_Expr_isAppOf(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Elab_Eqns_deltaLHS(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix(x_23, x_2, x_3, x_4, x_5, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_33 = lean_unsigned_to_nat(3u);
x_34 = l_Lean_Expr_isAppOfArity(x_30, x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4;
x_36 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_35, x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = l_Lean_Expr_appFn_x21(x_30);
lean_dec(x_30);
x_40 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
x_41 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11;
x_42 = l_Lean_Expr_isAppOf(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Elab_Eqns_deltaLHS(x_1, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix(x_44, x_2, x_3, x_4, x_5, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
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
else
{
lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_7);
if (x_52 == 0)
{
return x_7;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.WF.Eqns");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Eqns.0.Lean.Elab.WF.rwFixEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(31u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fix_eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(33u);
x_4 = lean_unsigned_to_nat(51u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_274 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_275 = lean_unsigned_to_nat(3u);
x_276 = l_Lean_Expr_isAppOfArity(x_8, x_274, x_275);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_8);
x_277 = lean_box(0);
x_10 = x_277;
goto block_273;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_278 = l_Lean_Expr_appFn_x21(x_8);
x_279 = l_Lean_Expr_appFn_x21(x_278);
x_280 = l_Lean_Expr_appArg_x21(x_279);
lean_dec(x_279);
x_281 = l_Lean_Expr_appArg_x21(x_278);
lean_dec(x_278);
x_282 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_10 = x_285;
goto block_273;
}
block_273:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4;
x_12 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = l_Lean_Expr_getAppFn(x_19);
x_22 = l_Lean_Expr_constLevels_x21(x_21);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6;
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux(x_19, x_25);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_19, x_28, x_30);
x_32 = l_Lean_mkAppN(x_24, x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_33 = lean_infer_type(x_32, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_68 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_69 = lean_unsigned_to_nat(3u);
x_70 = l_Lean_Expr_isAppOfArity(x_34, x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_34);
lean_free_object(x_16);
lean_free_object(x_14);
lean_free_object(x_10);
x_71 = lean_box(0);
x_36 = x_71;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = l_Lean_Expr_appFn_x21(x_34);
x_73 = l_Lean_Expr_appFn_x21(x_72);
x_74 = l_Lean_Expr_appArg_x21(x_73);
lean_dec(x_73);
x_75 = l_Lean_Expr_appArg_x21(x_72);
lean_dec(x_72);
x_76 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
lean_ctor_set(x_16, 1, x_76);
lean_ctor_set(x_16, 0, x_75);
lean_ctor_set(x_14, 0, x_74);
x_36 = x_10;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_1);
x_37 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8;
x_38 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_37, x_2, x_3, x_4, x_5, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Meta_mkEq(x_41, x_20, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
lean_inc(x_2);
x_46 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_43, x_45, x_2, x_3, x_4, x_5, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_47);
x_49 = l_Lean_Meta_mkEqTrans(x_32, x_47, x_2, x_3, x_4, x_5, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_assignExprMVar(x_1, x_50, x_2, x_3, x_4, x_5, x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = l_Lean_Expr_mvarId_x21(x_47);
lean_dec(x_47);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = l_Lean_Expr_mvarId_x21(x_47);
lean_dec(x_47);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_42);
if (x_63 == 0)
{
return x_42;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_32);
lean_free_object(x_16);
lean_dec(x_20);
lean_free_object(x_14);
lean_free_object(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_33);
if (x_77 == 0)
{
return x_33;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_33, 0);
x_79 = lean_ctor_get(x_33, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_81 = lean_ctor_get(x_16, 0);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_16);
x_83 = l_Lean_Expr_getAppFn(x_81);
x_84 = l_Lean_Expr_constLevels_x21(x_83);
x_85 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6;
x_86 = l_Lean_mkConst(x_85, x_84);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Expr_getAppNumArgsAux(x_81, x_87);
x_89 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7;
lean_inc(x_88);
x_90 = lean_mk_array(x_88, x_89);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_sub(x_88, x_91);
lean_dec(x_88);
x_93 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_81, x_90, x_92);
x_94 = l_Lean_mkAppN(x_86, x_93);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_94);
x_95 = lean_infer_type(x_94, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_128 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_129 = lean_unsigned_to_nat(3u);
x_130 = l_Lean_Expr_isAppOfArity(x_96, x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_96);
lean_free_object(x_14);
lean_free_object(x_10);
x_131 = lean_box(0);
x_98 = x_131;
goto block_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = l_Lean_Expr_appFn_x21(x_96);
x_133 = l_Lean_Expr_appFn_x21(x_132);
x_134 = l_Lean_Expr_appArg_x21(x_133);
lean_dec(x_133);
x_135 = l_Lean_Expr_appArg_x21(x_132);
lean_dec(x_132);
x_136 = l_Lean_Expr_appArg_x21(x_96);
lean_dec(x_96);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_14, 1, x_137);
lean_ctor_set(x_14, 0, x_134);
x_98 = x_10;
goto block_127;
}
block_127:
{
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_94);
lean_dec(x_82);
lean_dec(x_1);
x_99 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8;
x_100 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_99, x_2, x_3, x_4, x_5, x_97);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_104 = l_Lean_Meta_mkEq(x_103, x_82, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_box(0);
lean_inc(x_2);
x_108 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_105, x_107, x_2, x_3, x_4, x_5, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_109);
x_111 = l_Lean_Meta_mkEqTrans(x_94, x_109, x_2, x_3, x_4, x_5, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Meta_assignExprMVar(x_1, x_112, x_2, x_3, x_4, x_5, x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = l_Lean_Expr_mvarId_x21(x_109);
lean_dec(x_109);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_109);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_104, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_104, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_125 = x_104;
} else {
 lean_dec_ref(x_104);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_94);
lean_dec(x_82);
lean_free_object(x_14);
lean_free_object(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_ctor_get(x_95, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_95, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_140 = x_95;
} else {
 lean_dec_ref(x_95);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_142 = lean_ctor_get(x_14, 1);
lean_inc(x_142);
lean_dec(x_14);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Expr_getAppFn(x_143);
x_147 = l_Lean_Expr_constLevels_x21(x_146);
x_148 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6;
x_149 = l_Lean_mkConst(x_148, x_147);
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Lean_Expr_getAppNumArgsAux(x_143, x_150);
x_152 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7;
lean_inc(x_151);
x_153 = lean_mk_array(x_151, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_sub(x_151, x_154);
lean_dec(x_151);
x_156 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_143, x_153, x_155);
x_157 = l_Lean_mkAppN(x_149, x_156);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_157);
x_158 = lean_infer_type(x_157, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_191 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_192 = lean_unsigned_to_nat(3u);
x_193 = l_Lean_Expr_isAppOfArity(x_159, x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_159);
lean_dec(x_145);
lean_free_object(x_10);
x_194 = lean_box(0);
x_161 = x_194;
goto block_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = l_Lean_Expr_appFn_x21(x_159);
x_196 = l_Lean_Expr_appFn_x21(x_195);
x_197 = l_Lean_Expr_appArg_x21(x_196);
lean_dec(x_196);
x_198 = l_Lean_Expr_appArg_x21(x_195);
lean_dec(x_195);
x_199 = l_Lean_Expr_appArg_x21(x_159);
lean_dec(x_159);
if (lean_is_scalar(x_145)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_145;
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_10, 0, x_201);
x_161 = x_10;
goto block_190;
}
block_190:
{
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_157);
lean_dec(x_144);
lean_dec(x_1);
x_162 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8;
x_163 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_162, x_2, x_3, x_4, x_5, x_160);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_167 = l_Lean_Meta_mkEq(x_166, x_144, x_2, x_3, x_4, x_5, x_160);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_box(0);
lean_inc(x_2);
x_171 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_168, x_170, x_2, x_3, x_4, x_5, x_169);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_172);
x_174 = l_Lean_Meta_mkEqTrans(x_157, x_172, x_2, x_3, x_4, x_5, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Meta_assignExprMVar(x_1, x_175, x_2, x_3, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = l_Lean_Expr_mvarId_x21(x_172);
lean_dec(x_172);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_174, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_184 = x_174;
} else {
 lean_dec_ref(x_174);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_167, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_188 = x_167;
} else {
 lean_dec_ref(x_167);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_157);
lean_dec(x_145);
lean_dec(x_144);
lean_free_object(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_ctor_get(x_158, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_158, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_204 = x_158;
} else {
 lean_dec_ref(x_158);
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
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_206 = lean_ctor_get(x_10, 0);
lean_inc(x_206);
lean_dec(x_10);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_212 = l_Lean_Expr_getAppFn(x_209);
x_213 = l_Lean_Expr_constLevels_x21(x_212);
x_214 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6;
x_215 = l_Lean_mkConst(x_214, x_213);
x_216 = lean_unsigned_to_nat(0u);
x_217 = l_Lean_Expr_getAppNumArgsAux(x_209, x_216);
x_218 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7;
lean_inc(x_217);
x_219 = lean_mk_array(x_217, x_218);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_sub(x_217, x_220);
lean_dec(x_217);
x_222 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_209, x_219, x_221);
x_223 = l_Lean_mkAppN(x_215, x_222);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_223);
x_224 = lean_infer_type(x_223, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_257 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2;
x_258 = lean_unsigned_to_nat(3u);
x_259 = l_Lean_Expr_isAppOfArity(x_225, x_257, x_258);
if (x_259 == 0)
{
lean_object* x_260; 
lean_dec(x_225);
lean_dec(x_211);
lean_dec(x_208);
x_260 = lean_box(0);
x_227 = x_260;
goto block_256;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = l_Lean_Expr_appFn_x21(x_225);
x_262 = l_Lean_Expr_appFn_x21(x_261);
x_263 = l_Lean_Expr_appArg_x21(x_262);
lean_dec(x_262);
x_264 = l_Lean_Expr_appArg_x21(x_261);
lean_dec(x_261);
x_265 = l_Lean_Expr_appArg_x21(x_225);
lean_dec(x_225);
if (lean_is_scalar(x_211)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_211;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
if (lean_is_scalar(x_208)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_208;
}
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_227 = x_268;
goto block_256;
}
block_256:
{
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_223);
lean_dec(x_210);
lean_dec(x_1);
x_228 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8;
x_229 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_228, x_2, x_3, x_4, x_5, x_226);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_233 = l_Lean_Meta_mkEq(x_232, x_210, x_2, x_3, x_4, x_5, x_226);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_box(0);
lean_inc(x_2);
x_237 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_234, x_236, x_2, x_3, x_4, x_5, x_235);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_238);
x_240 = l_Lean_Meta_mkEqTrans(x_223, x_238, x_2, x_3, x_4, x_5, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Meta_assignExprMVar(x_1, x_241, x_2, x_3, x_4, x_5, x_242);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = l_Lean_Expr_mvarId_x21(x_238);
lean_dec(x_238);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_238);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_240, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_240, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_250 = x_240;
} else {
 lean_dec_ref(x_240);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_223);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_ctor_get(x_233, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_233, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_254 = x_233;
} else {
 lean_dec_ref(x_233);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_223);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = lean_ctor_get(x_224, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_224, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_271 = x_224;
} else {
 lean_dec_ref(x_224);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_7);
if (x_286 == 0)
{
return x_7;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_7, 0);
x_288 = lean_ctor_get(x_7, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_7);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1;
x_3 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_discharge_x3f___boxed), 9, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Meta_Simp_simpMatchCore_x3f(x_2, x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_11, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_11, 0, x_42);
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1(x_1, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_simpMatchWF_x3f_pre), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1;
x_2 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2;
x_3 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l_Lean_Meta_instantiateMVars(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Split_getSimpMatchContext___rarg(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_17 = l_Lean_Meta_Simp_main(x_11, x_14, x_16, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_Meta_applySimpResultToTarget(x_1, x_11, x_18, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_name_eq(x_1, x_22);
lean_dec(x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_name_eq(x_1, x_26);
lean_dec(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_simpMatchWF_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_simpMatchWF_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_simpMatchWF_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = lean_array_uget(x_3, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_1, x_2, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_6 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 6, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 9, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 10, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1;
x_3 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4;
x_4 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate equational theorem for '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Eqns_tryURefl(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Elab_Eqns_tryContradiction(x_1, x_5, x_6, x_7, x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Elab_WF_simpMatchWF_x3f(x_1, x_2, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_21 = l_Lean_Elab_Eqns_simpIf_x3f(x_1, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_1, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_29 = l_Lean_Meta_simpTargetStar(x_1, x_28, x_27, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
switch (lean_obj_tag(x_30)) {
case 0:
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_38 = l_Lean_Meta_casesOnStuckLHS_x3f(x_1, x_5, x_6, x_7, x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(x_1, x_41, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_3);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_50, 0, x_1);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_53, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1(x_3, x_2, x_56, x_5, x_6, x_7, x_8, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_42);
if (x_58 == 0)
{
return x_42;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_42, 0);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_42);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_38, 1);
x_64 = lean_ctor_get(x_38, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
lean_dec(x_39);
x_66 = lean_array_get_size(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_69 = lean_box(0);
lean_ctor_set(x_38, 0, x_69);
return x_38;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_66, x_66);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_71 = lean_box(0);
lean_ctor_set(x_38, 0, x_71);
return x_38;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_38);
x_72 = 0;
x_73 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_74 = lean_box(0);
x_75 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2(x_3, x_2, x_65, x_72, x_73, x_74, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_65);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_38, 1);
lean_inc(x_76);
lean_dec(x_38);
x_77 = lean_ctor_get(x_39, 0);
lean_inc(x_77);
lean_dec(x_39);
x_78 = lean_array_get_size(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_lt(x_79, x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_78, x_78);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
return x_85;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = lean_box(0);
x_89 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2(x_3, x_2, x_77, x_86, x_87, x_88, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_77);
return x_89;
}
}
}
}
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
lean_dec(x_29);
x_91 = lean_ctor_get(x_30, 0);
lean_inc(x_91);
lean_dec(x_30);
x_92 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_3, x_2, x_91, x_5, x_6, x_7, x_8, x_90);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_29);
if (x_93 == 0)
{
return x_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_29, 0);
x_95 = lean_ctor_get(x_29, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_29);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_24, 1);
lean_inc(x_97);
lean_dec(x_24);
x_98 = lean_ctor_get(x_25, 0);
lean_inc(x_98);
lean_dec(x_25);
x_99 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_3, x_2, x_98, x_5, x_6, x_7, x_8, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_24);
if (x_100 == 0)
{
return x_24;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_24, 0);
x_102 = lean_ctor_get(x_24, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_24);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_1);
x_104 = lean_ctor_get(x_21, 1);
lean_inc(x_104);
lean_dec(x_21);
x_105 = lean_ctor_get(x_22, 0);
lean_inc(x_105);
lean_dec(x_22);
x_106 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_3, x_2, x_105, x_5, x_6, x_7, x_8, x_104);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_21);
if (x_107 == 0)
{
return x_21;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_21, 0);
x_109 = lean_ctor_get(x_21, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_21);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_111 = lean_ctor_get(x_18, 1);
lean_inc(x_111);
lean_dec(x_18);
x_112 = lean_ctor_get(x_19, 0);
lean_inc(x_112);
lean_dec(x_19);
x_113 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_3, x_2, x_112, x_5, x_6, x_7, x_8, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_18);
if (x_114 == 0)
{
return x_18;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_18, 0);
x_116 = lean_ctor_get(x_18, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_18);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_14);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_14, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_14, 0, x_120);
return x_14;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_14, 1);
lean_inc(x_121);
lean_dec(x_14);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_10);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_10, 0);
lean_dec(x_125);
x_126 = lean_box(0);
lean_ctor_set(x_10, 0, x_126);
return x_10;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_10, 1);
lean_inc(x_127);
lean_dec(x_10);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eqns");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8;
x_24 = lean_st_ref_get(x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_10 = x_29;
x_11 = x_28;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_9, x_4, x_5, x_6, x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_10 = x_34;
x_11 = x_33;
goto block_23;
}
block_23:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1(x_3, x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
x_14 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_18, x_4, x_5, x_6, x_7, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1(x_3, x_2, x_1, x_20, x_4, x_5, x_6, x_7, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_intros(x_13, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix(x_17, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq(x_19, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go(x_2, x_3, x_22, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_instantiateMVars(x_11, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proving: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8;
x_24 = lean_st_ref_get(x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_10 = x_29;
x_11 = x_28;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_9, x_4, x_5, x_6, x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_10 = x_34;
x_11 = x_33;
goto block_23;
}
block_23:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2(x_3, x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_18, x_4, x_5, x_6, x_7, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2(x_3, x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_eq");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2;
x_17 = lean_name_append_index_after(x_16, x_15);
x_18 = l_Lean_Name_append(x_2, x_17);
lean_inc(x_18);
x_19 = lean_array_push(x_7, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof(x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_5, x_21, x_11, x_12, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_31, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_19);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_8, x_7);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get(x_21, x_5, x_7);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8;
x_67 = lean_st_ref_get(x_14, x_15);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = 0;
x_24 = x_72;
x_25 = x_71;
goto block_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_23, x_11, x_12, x_13, x_14, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
x_24 = x_77;
x_25 = x_76;
goto block_66;
}
block_66:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1(x_7, x_3, x_1, x_2, x_22, x_4, x_10, x_26, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_37;
x_10 = x_36;
x_15 = x_35;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_22);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_22);
x_44 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_23, x_46, x_11, x_12, x_13, x_14, x_25);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1(x_7, x_3, x_1, x_2, x_22, x_4, x_10, x_48, x_11, x_12, x_13, x_14, x_49);
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_60;
x_10 = x_59;
x_15 = x_58;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_15);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_15);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_11, x_12);
x_14 = l_Lean_mkConst(x_2, x_13);
x_15 = l_Lean_mkAppN(x_14, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_mkEq(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_6);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_19, x_6, x_7, x_8, x_9, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Elab_Eqns_mkEqnTypes(x_23, x_24, x_6, x_7, x_8, x_9, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_mkEqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = l_Lean_Elab_WF_mkEqns___closed__1;
x_11 = 0;
x_12 = l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(x_9, x_10, x_11);
lean_ctor_set(x_5, 0, x_12);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_mkPrivateName(x_16, x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkEqns___lambda__1), 10, 3);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_21, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4;
lean_inc(x_25);
x_29 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1(x_1, x_2, x_17, x_18, x_23, x_25, x_26, x_25, x_27, x_28, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
x_44 = lean_ctor_get(x_5, 2);
x_45 = lean_ctor_get(x_5, 3);
x_46 = lean_ctor_get(x_5, 4);
x_47 = lean_ctor_get(x_5, 5);
x_48 = lean_ctor_get(x_5, 6);
x_49 = lean_ctor_get(x_5, 7);
x_50 = lean_ctor_get(x_5, 8);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_5);
x_51 = l_Lean_Elab_WF_mkEqns___closed__1;
x_52 = 0;
x_53 = l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(x_42, x_51, x_52);
x_54 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set(x_54, 4, x_46);
lean_ctor_set(x_54, 5, x_47);
lean_ctor_set(x_54, 6, x_48);
lean_ctor_set(x_54, 7, x_49);
lean_ctor_set(x_54, 8, x_50);
x_55 = lean_st_ref_get(x_6, x_7);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_1);
x_59 = l_Lean_mkPrivateName(x_58, x_1);
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkEqns___lambda__1), 10, 3);
lean_closure_set(x_62, 0, x_60);
lean_closure_set(x_62, 1, x_1);
lean_closure_set(x_62, 2, x_2);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg), 7, 2);
lean_closure_set(x_63, 0, x_61);
lean_closure_set(x_63, 1, x_62);
lean_inc(x_6);
lean_inc(x_54);
lean_inc(x_4);
lean_inc(x_3);
x_64 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_63, x_3, x_4, x_54, x_6, x_57);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_array_get_size(x_65);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4;
lean_inc(x_67);
x_71 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1(x_1, x_2, x_59, x_60, x_65, x_67, x_68, x_67, x_69, x_70, x_3, x_4, x_54, x_6, x_66);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_64, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_64, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_82 = x_64;
} else {
 lean_dec_ref(x_64);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wfEqInfo");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_WF_instInhabitedEqnInfo;
x_3 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2;
x_4 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_WF_eqnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 5);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_2);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1;
x_17 = l_Lean_MapDeclarationExtension_insert___rarg(x_16, x_7, x_10, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_7 = x_17;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_registerEqnsInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_usize_of_nat(x_7);
x_9 = 0;
lean_inc(x_1);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1(x_8, x_9, x_1);
x_11 = lean_st_ref_take(x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 4);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
lean_ctor_set(x_12, 4, x_19);
x_20 = lean_st_ref_set(x_5, x_12, x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_7, x_7);
lean_dec(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
lean_ctor_set(x_12, 4, x_28);
x_29 = lean_st_ref_set(x_5, x_12, x_13);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2(x_2, x_3, x_10, x_1, x_9, x_8, x_15);
lean_dec(x_1);
x_37 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
lean_ctor_set(x_12, 4, x_37);
lean_ctor_set(x_12, 0, x_36);
x_38 = lean_st_ref_set(x_5, x_12, x_13);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
x_47 = lean_ctor_get(x_12, 2);
x_48 = lean_ctor_get(x_12, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_7);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_13);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_7, x_7);
lean_dec(x_7);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_48);
lean_ctor_set(x_60, 4, x_59);
x_61 = lean_st_ref_set(x_5, x_60, x_13);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2(x_2, x_3, x_10, x_1, x_9, x_8, x_45);
lean_dec(x_1);
x_67 = l_Lean_Elab_WF_registerEqnsInfo___closed__1;
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 2, x_47);
lean_ctor_set(x_68, 3, x_48);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_st_ref_set(x_5, x_68, x_13);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_registerEqnsInfo___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_registerEqnsInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_registerEqnsInfo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_WF_instInhabitedEqnInfo;
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1;
lean_inc(x_1);
x_14 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_12, x_13, x_11, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
uint8_t x_16; 
lean_free_object(x_7);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_Elab_WF_mkEqns(x_1, x_17, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_14, 0, x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_14);
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
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_Elab_WF_mkEqns(x_1, x_28, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_WF_instInhabitedEqnInfo;
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1;
lean_inc(x_1);
x_44 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_42, x_43, x_41, x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Elab_WF_mkEqns(x_1, x_47, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_50);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_WF_instInhabitedEqnInfo;
x_5 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1;
x_6 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_4, x_5, x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Elab_Eqns_getUnfoldFor_x3f(x_1, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_getUnfoldFor_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getUnfoldFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2;
x_6 = l_Lean_Meta_registerGetUnfoldEqnFn(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_WF_instInhabitedEqnInfo___closed__1 = _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__1();
l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2 = _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo___closed__2);
l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3 = _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo___closed__3);
l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4 = _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo___closed__4);
l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5 = _init_l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo___closed__5);
l_Lean_Elab_WF_instInhabitedEqnInfo = _init_l_Lean_Elab_WF_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_deltaLHSUntilFix___lambda__1___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_rwFixEq___lambda__1___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_hasWellFoundedFix___closed__1);
l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1 = _init_l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_simpMatchWF_x3f_pre___lambda__1___closed__1);
l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1 = _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__1);
l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2 = _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__2);
l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3 = _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__3);
l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4 = _init_l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_simpMatchWF_x3f___lambda__3___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___lambda__1___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof_go___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_mkProof___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_WF_mkEqns___spec__1___lambda__1___closed__2);
l_Lean_Elab_WF_mkEqns___closed__1 = _init_l_Lean_Elab_WF_mkEqns___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkEqns___closed__1);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__1);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651____closed__2);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1651_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_eqnInfoExt);
lean_dec_ref(res);
}l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_registerEqnsInfo___spec__2___closed__1);
l_Lean_Elab_WF_registerEqnsInfo___closed__1 = _init_l_Lean_Elab_WF_registerEqnsInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_registerEqnsInfo___closed__1);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__1);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816____closed__2);
res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Eqns___hyg_1816_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
