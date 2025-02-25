// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Init Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Rename Lean.Meta.Tactic.Intro Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_instInhabitedTerminationByElement;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
uint8_t l_Lean_Expr_isLit(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
static lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object**);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; 
lean_dec(x_7);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
{
size_t _tmp_3 = x_14;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_WF_instInhabitedTerminationByElement;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
x_6 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_5, x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.WF.Rel");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackMutual.go");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
x_3 = lean_unsigned_to_nat(26u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_array_push(x_5, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Cases_cases(x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_22);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
x_28 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_fget(x_22, x_29);
x_31 = lean_array_fget(x_22, x_14);
lean_dec(x_22);
x_32 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_array_get(x_36, x_35, x_29);
lean_dec(x_35);
x_38 = l_Lean_Expr_fvarId_x21(x_37);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_array_get(x_36, x_40, x_29);
lean_dec(x_40);
x_42 = l_Lean_Expr_fvarId_x21(x_41);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_5, x_44);
x_2 = x_32;
x_3 = x_34;
x_4 = x_38;
x_5 = x_45;
x_12 = x_23;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_13 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(x_1, x_11, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackUnary.go");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(50u);
x_4 = lean_unsigned_to_nat(85u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_instInhabitedName;
x_19 = l_Array_back___rarg(x_18, x_3);
lean_dec(x_3);
x_20 = l_Lean_Meta_rename(x_4, x_5, x_19, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_nat_add(x_6, x_2);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_array_get(x_22, x_3, x_21);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_29 = lean_array_push(x_28, x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Meta_Cases_cases(x_4, x_5, x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_31);
x_34 = lean_nat_dec_eq(x_33, x_15);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
x_36 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_31, x_37);
lean_dec(x_31);
x_39 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_instInhabitedExpr;
x_44 = lean_array_get(x_43, x_42, x_15);
lean_dec(x_42);
x_45 = l_Lean_Expr_fvarId_x21(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_6, x_3, x_1, x_39, x_41, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_30);
if (x_47 == 0)
{
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("i: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", varNames: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", goal: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_42 = lean_st_ref_get(x_12, x_13);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = 0;
x_15 = x_47;
x_16 = x_46;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_15 = x_52;
x_16 = x_51;
goto block_41;
}
block_41:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_4);
x_19 = l_Nat_repr(x_4);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_2);
x_26 = lean_array_to_list(lean_box(0), x_2);
x_27 = lean_box(0);
x_28 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_26, x_27);
x_29 = l_Lean_MessageData_ofList(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_5);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_14, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Lean_Expr_fvarId_x21(x_13);
lean_inc(x_6);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = l_Lean_instInhabitedSyntax;
x_21 = lean_array_get(x_20, x_1, x_4);
x_22 = l_Lean_Syntax_isIdent(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_get_size(x_7);
x_26 = lean_nat_sub(x_25, x_2);
lean_dec(x_25);
x_27 = lean_nat_add(x_26, x_4);
lean_dec(x_26);
x_28 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
x_29 = lean_array_set(x_7, x_27, x_28);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_30;
x_7 = x_29;
goto _start;
}
}
else
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_14);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_14);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
lean_inc(x_1);
x_20 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_2);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
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
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
lean_inc(x_1);
x_38 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_5, x_48);
x_5 = x_49;
x_6 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; 
lean_inc(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_18 = x_29;
x_19 = x_12;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_18 = x_38;
x_19 = x_12;
goto block_28;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_30, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_33, x_34);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_34, x_44);
lean_dec(x_34);
lean_ctor_set(x_30, 1, x_45);
x_46 = l_Lean_LocalDecl_userName(x_31);
x_47 = lean_name_eq(x_46, x_43);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_Meta_rename(x_32, x_48, x_43, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_30);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_53;
x_19 = x_51;
goto block_28;
}
else
{
uint8_t x_54; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
lean_dec(x_31);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_32);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_18 = x_59;
x_19 = x_12;
goto block_28;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_30);
x_60 = lean_array_fget(x_33, x_34);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_34, x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_35);
x_64 = l_Lean_LocalDecl_userName(x_31);
x_65 = lean_name_eq(x_64, x_60);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_67 = l_Lean_Meta_rename(x_32, x_66, x_60, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_18 = x_71;
x_19 = x_69;
goto block_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_31);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_18 = x_77;
x_19 = x_12;
goto block_28;
}
}
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_4, x_25);
x_4 = x_26;
x_5 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_array_get_size(x_11);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_12, x_11, x_15, x_16, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
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
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_array_get_size(x_34);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_35, x_34, x_38, x_39, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_44, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_30; 
lean_inc(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_18 = x_30;
x_19 = x_12;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_18 = x_39;
x_19 = x_12;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_31, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = lean_array_fget(x_34, x_35);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_35, x_45);
lean_dec(x_35);
lean_ctor_set(x_31, 1, x_46);
x_47 = l_Lean_LocalDecl_userName(x_32);
x_48 = lean_name_eq(x_47, x_44);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_Meta_rename(x_33, x_49, x_44, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_18 = x_54;
x_19 = x_52;
goto block_29;
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_33);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_18 = x_60;
x_19 = x_12;
goto block_29;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_31);
x_61 = lean_array_fget(x_34, x_35);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_35, x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
x_65 = l_Lean_LocalDecl_userName(x_32);
x_66 = lean_name_eq(x_65, x_61);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_Meta_rename(x_33, x_67, x_61, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_18 = x_72;
x_19 = x_70;
goto block_29;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_61);
lean_dec(x_32);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_33);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_18 = x_78;
x_19 = x_12;
goto block_29;
}
}
}
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_22, x_21, x_25, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_11, x_12, x_12, x_13, x_12, x_14, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many variable names");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_6);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_15, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_15);
x_23 = l_Lean_instInhabitedSyntax;
x_24 = lean_array_get(x_23, x_18, x_17);
lean_dec(x_17);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_6);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed), 10, 1);
lean_closure_set(x_14, 0, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_getMVarDecl(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_16);
x_22 = l_Array_toSubarray___rarg(x_16, x_21, x_2);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_16);
x_31 = lean_nat_sub(x_30, x_2);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_2, x_16, x_31, x_21, x_29, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_sub(x_9, x_1);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_ctor_get(x_12, 5);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(x_15, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_14, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SizeOf");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sizeOf");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_nat_add(x_17, x_19);
lean_ctor_set(x_15, 0, x_26);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_28 = lean_array_push(x_27, x_13);
x_29 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_mkAppM(x_29, x_28, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_whnfD(x_31, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_isLit(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
size_t x_37; size_t x_38; 
lean_dec(x_17);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; 
x_40 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_40);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_9 = x_35;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_45);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_3 = x_47;
x_9 = x_44;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_50);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_9 = x_49;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
x_54 = lean_nat_add(x_17, x_19);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_18);
lean_ctor_set(x_55, 2, x_19);
x_56 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_57 = lean_array_push(x_56, x_13);
x_58 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_mkAppM(x_58, x_57, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_whnfD(x_60, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_isLit(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
size_t x_66; size_t x_67; 
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_55);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_3 = x_67;
x_9 = x_64;
goto _start;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; 
x_69 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_55);
x_70 = 1;
x_71 = lean_usize_add(x_3, x_70);
x_3 = x_71;
x_9 = x_64;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_74);
lean_ctor_set(x_4, 0, x_55);
x_75 = 1;
x_76 = lean_usize_add(x_3, x_75);
x_3 = x_76;
x_9 = x_73;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; 
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_79);
lean_ctor_set(x_4, 0, x_55);
x_80 = 1;
x_81 = lean_usize_add(x_3, x_80);
x_3 = x_81;
x_9 = x_78;
goto _start;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_4, 0);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_4);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc(x_87);
x_88 = lean_nat_dec_lt(x_85, x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_85, x_87);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
x_94 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_95 = lean_array_push(x_94, x_13);
x_96 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_97 = l_Lean_Meta_mkAppM(x_96, x_95, x_5, x_6, x_7, x_8, x_9);
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
x_100 = l_Lean_Meta_whnfD(x_98, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_isLit(x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; size_t x_105; size_t x_106; 
lean_dec(x_85);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_84);
x_105 = 1;
x_106 = lean_usize_add(x_3, x_105);
x_3 = x_106;
x_4 = x_104;
x_9 = x_102;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; 
x_108 = lean_array_push(x_84, x_85);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_108);
x_110 = 1;
x_111 = lean_usize_add(x_3, x_110);
x_3 = x_111;
x_4 = x_109;
x_9 = x_102;
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; 
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_114 = lean_array_push(x_84, x_85);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_93);
lean_ctor_set(x_115, 1, x_114);
x_116 = 1;
x_117 = lean_usize_add(x_3, x_116);
x_3 = x_117;
x_4 = x_115;
x_9 = x_113;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; 
x_119 = lean_ctor_get(x_97, 1);
lean_inc(x_119);
lean_dec(x_97);
x_120 = lean_array_push(x_84, x_85);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_93);
lean_ctor_set(x_121, 1, x_120);
x_122 = 1;
x_123 = lean_usize_add(x_3, x_122);
x_3 = x_123;
x_4 = x_121;
x_9 = x_119;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___rarg(x_2, x_1, x_13);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_14, x_18, x_20, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
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
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_4, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_nat_add(x_4, x_15);
lean_inc(x_6);
lean_inc(x_10);
x_19 = lean_array_push(x_10, x_6);
x_20 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_18, x_19, x_11);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_30 = lean_box(0);
x_5 = x_16;
x_6 = x_29;
x_9 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_33 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
x_9 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_push(x_6, x_5);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_16, x_18, x_19, x_5, x_6);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_6 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_15);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_19, x_20, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_assignExprMVar(x_1, x_22, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_16, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_16, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_22, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_33);
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_20, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_20, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_20, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_34, x_35);
x_44 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
lean_ctor_set(x_20, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_43);
lean_inc(x_1);
x_45 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_46, x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; size_t x_51; size_t x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 1;
x_52 = lean_usize_add(x_4, x_51);
x_4 = x_52;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_43);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_62 = lean_array_fget(x_34, x_35);
x_63 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
lean_inc(x_1);
x_65 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_66, x_68, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; size_t x_71; size_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_ctor_set(x_5, 1, x_64);
x_71 = 1;
x_72 = lean_usize_add(x_4, x_71);
x_4 = x_72;
x_12 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_16);
x_82 = lean_array_fget(x_22, x_23);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_23, x_83);
lean_dec(x_23);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_24);
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_20, 2);
lean_inc(x_88);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_12);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_91 = x_20;
} else {
 lean_dec_ref(x_20);
 x_91 = lean_box(0);
}
x_92 = lean_array_fget(x_86, x_87);
x_93 = lean_nat_add(x_87, x_83);
lean_dec(x_87);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_88);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_92);
lean_inc(x_1);
x_95 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_82, x_1, x_18, x_17, x_92, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_96);
x_98 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_98, 0, x_96);
lean_closure_set(x_98, 1, x_92);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_96, x_98, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; size_t x_101; size_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_ctor_set(x_5, 1, x_94);
lean_ctor_set(x_5, 0, x_85);
x_101 = 1;
x_102 = lean_usize_add(x_4, x_101);
x_4 = x_102;
x_12 = x_100;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_110 = x_95;
} else {
 lean_dec_ref(x_95);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_5, 1);
lean_inc(x_112);
lean_dec(x_5);
x_113 = lean_ctor_get(x_16, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_16, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_16, 2);
lean_inc(x_115);
x_116 = lean_nat_dec_lt(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_16);
lean_ctor_set(x_117, 1, x_112);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_12);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_119 = x_16;
} else {
 lean_dec_ref(x_16);
 x_119 = lean_box(0);
}
x_120 = lean_array_fget(x_113, x_114);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_114, x_121);
lean_dec(x_114);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_115);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_112, 2);
lean_inc(x_126);
x_127 = lean_nat_dec_lt(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_112);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_12);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_130 = x_112;
} else {
 lean_dec_ref(x_112);
 x_130 = lean_box(0);
}
x_131 = lean_array_fget(x_124, x_125);
x_132 = lean_nat_add(x_125, x_121);
lean_dec(x_125);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_126);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_131);
lean_inc(x_1);
x_134 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_120, x_1, x_18, x_17, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_135);
x_137 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_137, 0, x_135);
lean_closure_set(x_137, 1, x_131);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_138 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_135, x_137, x_6, x_7, x_8, x_9, x_10, x_11, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_133);
x_141 = 1;
x_142 = lean_usize_add(x_4, x_141);
x_4 = x_142;
x_5 = x_140;
x_12 = x_139;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invImage");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to apply 'invImage'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_11, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_11, 3, x_16);
x_17 = lean_box(0);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_17, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_22, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_27 = l_Lean_Meta_apply(x_21, x_24, x_26, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_31 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_35 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_39 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_Meta_intro1Core(x_42, x_44, x_9, x_10, x_11, x_12, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_50 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_49, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_get_size(x_4);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_toSubarray___rarg(x_4, x_54, x_53);
x_56 = lean_array_get_size(x_3);
x_57 = l_Array_toSubarray___rarg(x_3, x_54, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_array_get_size(x_51);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_51, x_60, x_61, x_58, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_51);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_43);
x_64 = l_Lean_mkMVar(x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_65 = lean_infer_type(x_64, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_69 = l_Lean_Meta_synthInstance(x_66, x_68, x_9, x_10, x_11, x_12, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_assignExprMVar(x_43, x_70, x_9, x_10, x_11, x_12, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_mkMVar(x_21);
lean_inc(x_10);
x_75 = l_Lean_Meta_instantiateMVars(x_74, x_9, x_10, x_11, x_12, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_apply_8(x_6, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_69);
if (x_79 == 0)
{
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_62);
if (x_87 == 0)
{
return x_62;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_62, 0);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_50);
if (x_91 == 0)
{
return x_50;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_50, 0);
x_93 = lean_ctor_get(x_50, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_50);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_45);
if (x_95 == 0)
{
return x_45;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_45, 0);
x_97 = lean_ctor_get(x_45, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_45);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_27, 1);
lean_inc(x_99);
lean_dec(x_27);
x_100 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_101 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_100, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_101;
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_27);
if (x_102 == 0)
{
return x_27;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_27, 0);
x_104 = lean_ctor_get(x_27, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_27);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_23);
if (x_106 == 0)
{
return x_23;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_23, 0);
x_108 = lean_ctor_get(x_23, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_23);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
x_112 = lean_ctor_get(x_11, 2);
x_113 = lean_ctor_get(x_11, 3);
x_114 = lean_ctor_get(x_11, 4);
x_115 = lean_ctor_get(x_11, 5);
x_116 = lean_ctor_get(x_11, 6);
x_117 = lean_ctor_get(x_11, 7);
x_118 = lean_ctor_get(x_11, 8);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_119 = l_Lean_replaceRef(x_1, x_113);
lean_dec(x_113);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_111);
lean_ctor_set(x_120, 2, x_112);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_114);
lean_ctor_set(x_120, 5, x_115);
lean_ctor_set(x_120, 6, x_116);
lean_ctor_set(x_120, 7, x_117);
lean_ctor_set(x_120, 8, x_118);
x_121 = lean_box(0);
lean_inc(x_9);
x_122 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_121, x_9, x_10, x_120, x_12, x_13);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Expr_mvarId_x21(x_123);
lean_dec(x_123);
x_126 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_126, x_9, x_10, x_120, x_12, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_125);
x_131 = l_Lean_Meta_apply(x_125, x_128, x_130, x_9, x_10, x_120, x_12, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_135 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_134, x_7, x_8, x_9, x_10, x_120, x_12, x_133);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_135;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_dec(x_131);
x_138 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_139 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_138, x_7, x_8, x_9, x_10, x_120, x_12, x_137);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_139;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
lean_dec(x_131);
x_142 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_143 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_142, x_7, x_8, x_9, x_10, x_120, x_12, x_141);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_131, 1);
lean_inc(x_145);
lean_dec(x_131);
x_146 = lean_ctor_get(x_132, 0);
lean_inc(x_146);
lean_dec(x_132);
x_147 = lean_ctor_get(x_136, 0);
lean_inc(x_147);
lean_dec(x_136);
x_148 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_149 = l_Lean_Meta_intro1Core(x_146, x_148, x_9, x_10, x_120, x_12, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_154 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_153, x_152, x_7, x_8, x_9, x_10, x_120, x_12, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_array_get_size(x_4);
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Array_toSubarray___rarg(x_4, x_158, x_157);
x_160 = lean_array_get_size(x_3);
x_161 = l_Array_toSubarray___rarg(x_3, x_158, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
x_163 = lean_array_get_size(x_155);
x_164 = lean_usize_of_nat(x_163);
lean_dec(x_163);
x_165 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_155, x_164, x_165, x_162, x_7, x_8, x_9, x_10, x_120, x_12, x_156);
lean_dec(x_155);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
lean_inc(x_147);
x_168 = l_Lean_mkMVar(x_147);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_169 = lean_infer_type(x_168, x_9, x_10, x_120, x_12, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_box(0);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_173 = l_Lean_Meta_synthInstance(x_170, x_172, x_9, x_10, x_120, x_12, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Meta_assignExprMVar(x_147, x_174, x_9, x_10, x_120, x_12, x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_mkMVar(x_125);
lean_inc(x_10);
x_179 = l_Lean_Meta_instantiateMVars(x_178, x_9, x_10, x_120, x_12, x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_apply_8(x_6, x_180, x_7, x_8, x_9, x_10, x_120, x_12, x_181);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_183 = lean_ctor_get(x_173, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_173, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_185 = x_173;
} else {
 lean_dec_ref(x_173);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_187 = lean_ctor_get(x_169, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_169, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_189 = x_169;
} else {
 lean_dec_ref(x_169);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_191 = lean_ctor_get(x_166, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_166, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_193 = x_166;
} else {
 lean_dec_ref(x_166);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_ctor_get(x_154, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_154, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_197 = x_154;
} else {
 lean_dec_ref(x_154);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_ctor_get(x_149, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_201 = x_149;
} else {
 lean_dec_ref(x_149);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_ctor_get(x_131, 1);
lean_inc(x_203);
lean_dec(x_131);
x_204 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_205 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_204, x_7, x_8, x_9, x_10, x_120, x_12, x_203);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_205;
}
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = lean_ctor_get(x_131, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_131, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_208 = x_131;
} else {
 lean_dec_ref(x_131);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_ctor_get(x_127, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_127, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_212 = x_127;
} else {
 lean_dec_ref(x_127);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1), 13, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
x_16 = l_Lean_Elab_Term_withDeclName___rarg(x_2, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
lean_inc(x_1);
x_19 = lean_array_push(x_6, x_1);
x_20 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_18;
x_3 = x_20;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 3);
x_17 = 0;
lean_inc(x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
x_19 = lean_array_push(x_6, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tupleTail");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_13, x_12);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_34; uint8_t x_35; 
x_24 = lean_array_uget(x_11, x_13);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 2);
lean_inc(x_46);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_24);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_14);
x_25 = x_48;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_38, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_38, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_38, 0);
lean_dec(x_52);
x_53 = lean_nat_add(x_44, x_46);
lean_ctor_set(x_38, 0, x_53);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_39, 2);
lean_inc(x_56);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_44);
lean_dec(x_24);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_14);
x_25 = x_58;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_39);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_60 = lean_ctor_get(x_39, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_39, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_39, 0);
lean_dec(x_62);
x_63 = lean_array_fget(x_54, x_55);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_55, x_64);
lean_dec(x_55);
lean_ctor_set(x_39, 1, x_65);
x_66 = lean_ctor_get(x_42, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 2);
lean_inc(x_68);
x_69 = lean_nat_dec_lt(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_44);
lean_dec(x_24);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_14);
x_25 = x_70;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_71; 
lean_free_object(x_37);
lean_free_object(x_14);
lean_free_object(x_34);
x_71 = !lean_is_exclusive(x_42);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_72 = lean_ctor_get(x_42, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_42, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_42, 0);
lean_dec(x_74);
x_75 = lean_array_fget(x_66, x_67);
x_76 = lean_nat_add(x_67, x_64);
lean_dec(x_67);
lean_ctor_set(x_42, 1, x_76);
lean_inc(x_6);
lean_inc(x_8);
x_77 = lean_array_push(x_8, x_6);
x_78 = lean_nat_sub(x_75, x_63);
lean_dec(x_63);
lean_dec(x_75);
x_79 = lean_nat_sub(x_78, x_64);
lean_dec(x_78);
x_80 = lean_unsigned_to_nat(0u);
lean_inc(x_79);
lean_inc(x_9);
x_81 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_79, x_80, x_79, x_64, x_77, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_nat_dec_lt(x_64, x_10);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_44);
lean_inc(x_19);
x_85 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_19, 8);
lean_inc(x_88);
x_89 = lean_st_ref_get(x_20, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_environment_main_module(x_92);
x_94 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_95 = lean_name_mk_string(x_7, x_94);
x_96 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_97 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 2, x_97);
x_99 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_88);
lean_inc(x_93);
x_100 = l_Lean_addMacroScope(x_93, x_99, x_88);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_5);
lean_inc(x_86);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_98);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_102);
lean_inc(x_4);
x_104 = l_Lean_addMacroScope(x_93, x_4, x_88);
lean_inc(x_5);
lean_inc(x_3);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_5);
lean_inc(x_8);
x_106 = lean_array_push(x_8, x_105);
x_107 = lean_box(2);
x_108 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_106);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_111 = lean_array_push(x_110, x_103);
x_112 = lean_array_push(x_111, x_109);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_95);
lean_ctor_set(x_113, 2, x_112);
x_114 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_82, x_42, x_38, x_39, x_43, x_113, x_15, x_16, x_17, x_18, x_19, x_20, x_91);
lean_dec(x_24);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_25 = x_115;
x_26 = x_116;
goto block_33;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_19);
x_117 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_83);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_19, 8);
lean_inc(x_120);
x_121 = lean_st_ref_get(x_20, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_environment_main_module(x_124);
x_126 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_127 = lean_name_mk_string(x_7, x_126);
x_128 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_118);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_131 = lean_name_mk_string(x_7, x_130);
x_132 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_133 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_2);
lean_ctor_set(x_134, 2, x_133);
x_135 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_120);
lean_inc(x_125);
x_136 = l_Lean_addMacroScope(x_125, x_135, x_120);
x_137 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_5);
lean_inc(x_118);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_118);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_4);
x_140 = l_Lean_addMacroScope(x_125, x_4, x_120);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_118);
x_141 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_141, 0, x_118);
lean_ctor_set(x_141, 1, x_3);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_5);
lean_inc(x_8);
x_142 = lean_array_push(x_8, x_141);
x_143 = lean_box(2);
x_144 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_142);
x_146 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_147 = lean_array_push(x_146, x_139);
x_148 = lean_array_push(x_147, x_145);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_131);
lean_ctor_set(x_149, 2, x_148);
x_150 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_151 = lean_name_mk_string(x_7, x_150);
x_152 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_118);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_118);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Nat_repr(x_44);
x_155 = l_Lean_numLitKind;
x_156 = l_Lean_Syntax_mkLit(x_155, x_154, x_143);
lean_inc(x_8);
x_157 = lean_array_push(x_8, x_156);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_144);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_array_push(x_146, x_153);
x_160 = lean_array_push(x_159, x_158);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_143);
lean_ctor_set(x_161, 1, x_151);
lean_ctor_set(x_161, 2, x_160);
lean_inc(x_8);
x_162 = lean_array_push(x_8, x_161);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_143);
lean_ctor_set(x_163, 1, x_144);
lean_ctor_set(x_163, 2, x_162);
x_164 = lean_array_push(x_146, x_149);
x_165 = lean_array_push(x_164, x_163);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_143);
lean_ctor_set(x_166, 1, x_144);
lean_ctor_set(x_166, 2, x_165);
x_167 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_118);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_170 = lean_array_push(x_169, x_129);
x_171 = lean_array_push(x_170, x_166);
x_172 = lean_array_push(x_171, x_168);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_143);
lean_ctor_set(x_173, 1, x_127);
lean_ctor_set(x_173, 2, x_172);
x_174 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_82, x_42, x_38, x_39, x_43, x_173, x_15, x_16, x_17, x_18, x_19, x_20, x_123);
lean_dec(x_24);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_25 = x_175;
x_26 = x_176;
goto block_33;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_42);
x_177 = lean_array_fget(x_66, x_67);
x_178 = lean_nat_add(x_67, x_64);
lean_dec(x_67);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_66);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_68);
lean_inc(x_6);
lean_inc(x_8);
x_180 = lean_array_push(x_8, x_6);
x_181 = lean_nat_sub(x_177, x_63);
lean_dec(x_63);
lean_dec(x_177);
x_182 = lean_nat_sub(x_181, x_64);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(0u);
lean_inc(x_182);
lean_inc(x_9);
x_184 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_182, x_183, x_182, x_64, x_180, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_dec_lt(x_64, x_10);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_44);
lean_inc(x_19);
x_188 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_186);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_19, 8);
lean_inc(x_191);
x_192 = lean_st_ref_get(x_20, x_190);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_environment_main_module(x_195);
x_197 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_198 = lean_name_mk_string(x_7, x_197);
x_199 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_200 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_2);
lean_ctor_set(x_201, 2, x_200);
x_202 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_191);
lean_inc(x_196);
x_203 = l_Lean_addMacroScope(x_196, x_202, x_191);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_5);
lean_inc(x_189);
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_189);
lean_ctor_set(x_206, 1, x_201);
lean_ctor_set(x_206, 2, x_203);
lean_ctor_set(x_206, 3, x_205);
lean_inc(x_4);
x_207 = l_Lean_addMacroScope(x_196, x_4, x_191);
lean_inc(x_5);
lean_inc(x_3);
x_208 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_208, 0, x_189);
lean_ctor_set(x_208, 1, x_3);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_208, 3, x_5);
lean_inc(x_8);
x_209 = lean_array_push(x_8, x_208);
x_210 = lean_box(2);
x_211 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_209);
x_213 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_214 = lean_array_push(x_213, x_206);
x_215 = lean_array_push(x_214, x_212);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_185, x_179, x_38, x_39, x_43, x_216, x_15, x_16, x_17, x_18, x_19, x_20, x_194);
lean_dec(x_24);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_25 = x_218;
x_26 = x_219;
goto block_33;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_inc(x_19);
x_220 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_186);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_19, 8);
lean_inc(x_223);
x_224 = lean_st_ref_get(x_20, x_222);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_environment_main_module(x_227);
x_229 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_230 = lean_name_mk_string(x_7, x_229);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_221);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_221);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_234 = lean_name_mk_string(x_7, x_233);
x_235 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_236 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_237 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_2);
lean_ctor_set(x_237, 2, x_236);
x_238 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_223);
lean_inc(x_228);
x_239 = l_Lean_addMacroScope(x_228, x_238, x_223);
x_240 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_5);
lean_inc(x_221);
x_242 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_242, 0, x_221);
lean_ctor_set(x_242, 1, x_237);
lean_ctor_set(x_242, 2, x_239);
lean_ctor_set(x_242, 3, x_241);
lean_inc(x_4);
x_243 = l_Lean_addMacroScope(x_228, x_4, x_223);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_221);
x_244 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_244, 0, x_221);
lean_ctor_set(x_244, 1, x_3);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_5);
lean_inc(x_8);
x_245 = lean_array_push(x_8, x_244);
x_246 = lean_box(2);
x_247 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_245);
x_249 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_250 = lean_array_push(x_249, x_242);
x_251 = lean_array_push(x_250, x_248);
x_252 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_234);
lean_ctor_set(x_252, 2, x_251);
x_253 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_254 = lean_name_mk_string(x_7, x_253);
x_255 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_221);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_221);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Nat_repr(x_44);
x_258 = l_Lean_numLitKind;
x_259 = l_Lean_Syntax_mkLit(x_258, x_257, x_246);
lean_inc(x_8);
x_260 = lean_array_push(x_8, x_259);
x_261 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_261, 0, x_246);
lean_ctor_set(x_261, 1, x_247);
lean_ctor_set(x_261, 2, x_260);
x_262 = lean_array_push(x_249, x_256);
x_263 = lean_array_push(x_262, x_261);
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_246);
lean_ctor_set(x_264, 1, x_254);
lean_ctor_set(x_264, 2, x_263);
lean_inc(x_8);
x_265 = lean_array_push(x_8, x_264);
x_266 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_266, 0, x_246);
lean_ctor_set(x_266, 1, x_247);
lean_ctor_set(x_266, 2, x_265);
x_267 = lean_array_push(x_249, x_252);
x_268 = lean_array_push(x_267, x_266);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_246);
lean_ctor_set(x_269, 1, x_247);
lean_ctor_set(x_269, 2, x_268);
x_270 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_271 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_271, 0, x_221);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_273 = lean_array_push(x_272, x_232);
x_274 = lean_array_push(x_273, x_269);
x_275 = lean_array_push(x_274, x_271);
x_276 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_276, 0, x_246);
lean_ctor_set(x_276, 1, x_230);
lean_ctor_set(x_276, 2, x_275);
x_277 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_185, x_179, x_38, x_39, x_43, x_276, x_15, x_16, x_17, x_18, x_19, x_20, x_226);
lean_dec(x_24);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_25 = x_278;
x_26 = x_279;
goto block_33;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
lean_dec(x_39);
x_280 = lean_array_fget(x_54, x_55);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_add(x_55, x_281);
lean_dec(x_55);
x_283 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_283, 0, x_54);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_283, 2, x_56);
x_284 = lean_ctor_get(x_42, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_42, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_42, 2);
lean_inc(x_286);
x_287 = lean_nat_dec_lt(x_285, x_286);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_280);
lean_dec(x_44);
lean_dec(x_24);
lean_ctor_set(x_14, 0, x_283);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_14);
x_25 = x_288;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_free_object(x_37);
lean_free_object(x_14);
lean_free_object(x_34);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_289 = x_42;
} else {
 lean_dec_ref(x_42);
 x_289 = lean_box(0);
}
x_290 = lean_array_fget(x_284, x_285);
x_291 = lean_nat_add(x_285, x_281);
lean_dec(x_285);
if (lean_is_scalar(x_289)) {
 x_292 = lean_alloc_ctor(0, 3, 0);
} else {
 x_292 = x_289;
}
lean_ctor_set(x_292, 0, x_284);
lean_ctor_set(x_292, 1, x_291);
lean_ctor_set(x_292, 2, x_286);
lean_inc(x_6);
lean_inc(x_8);
x_293 = lean_array_push(x_8, x_6);
x_294 = lean_nat_sub(x_290, x_280);
lean_dec(x_280);
lean_dec(x_290);
x_295 = lean_nat_sub(x_294, x_281);
lean_dec(x_294);
x_296 = lean_unsigned_to_nat(0u);
lean_inc(x_295);
lean_inc(x_9);
x_297 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_295, x_296, x_295, x_281, x_293, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_295);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_nat_dec_lt(x_281, x_10);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_44);
lean_inc(x_19);
x_301 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_299);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_19, 8);
lean_inc(x_304);
x_305 = lean_st_ref_get(x_20, x_303);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_environment_main_module(x_308);
x_310 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_311 = lean_name_mk_string(x_7, x_310);
x_312 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_313 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_2);
lean_ctor_set(x_314, 2, x_313);
x_315 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_304);
lean_inc(x_309);
x_316 = l_Lean_addMacroScope(x_309, x_315, x_304);
x_317 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_5);
lean_inc(x_302);
x_319 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_319, 0, x_302);
lean_ctor_set(x_319, 1, x_314);
lean_ctor_set(x_319, 2, x_316);
lean_ctor_set(x_319, 3, x_318);
lean_inc(x_4);
x_320 = l_Lean_addMacroScope(x_309, x_4, x_304);
lean_inc(x_5);
lean_inc(x_3);
x_321 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_321, 0, x_302);
lean_ctor_set(x_321, 1, x_3);
lean_ctor_set(x_321, 2, x_320);
lean_ctor_set(x_321, 3, x_5);
lean_inc(x_8);
x_322 = lean_array_push(x_8, x_321);
x_323 = lean_box(2);
x_324 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
lean_ctor_set(x_325, 2, x_322);
x_326 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_327 = lean_array_push(x_326, x_319);
x_328 = lean_array_push(x_327, x_325);
x_329 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_329, 0, x_323);
lean_ctor_set(x_329, 1, x_311);
lean_ctor_set(x_329, 2, x_328);
x_330 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_298, x_292, x_38, x_283, x_43, x_329, x_15, x_16, x_17, x_18, x_19, x_20, x_307);
lean_dec(x_24);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_25 = x_331;
x_26 = x_332;
goto block_33;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_inc(x_19);
x_333 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_299);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_ctor_get(x_19, 8);
lean_inc(x_336);
x_337 = lean_st_ref_get(x_20, x_335);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_environment_main_module(x_340);
x_342 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_343 = lean_name_mk_string(x_7, x_342);
x_344 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_334);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_334);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_347 = lean_name_mk_string(x_7, x_346);
x_348 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_349 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_350 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_2);
lean_ctor_set(x_350, 2, x_349);
x_351 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_336);
lean_inc(x_341);
x_352 = l_Lean_addMacroScope(x_341, x_351, x_336);
x_353 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_5);
lean_inc(x_334);
x_355 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_355, 0, x_334);
lean_ctor_set(x_355, 1, x_350);
lean_ctor_set(x_355, 2, x_352);
lean_ctor_set(x_355, 3, x_354);
lean_inc(x_4);
x_356 = l_Lean_addMacroScope(x_341, x_4, x_336);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_334);
x_357 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_357, 0, x_334);
lean_ctor_set(x_357, 1, x_3);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set(x_357, 3, x_5);
lean_inc(x_8);
x_358 = lean_array_push(x_8, x_357);
x_359 = lean_box(2);
x_360 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_361, 2, x_358);
x_362 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_363 = lean_array_push(x_362, x_355);
x_364 = lean_array_push(x_363, x_361);
x_365 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_365, 0, x_359);
lean_ctor_set(x_365, 1, x_347);
lean_ctor_set(x_365, 2, x_364);
x_366 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_367 = lean_name_mk_string(x_7, x_366);
x_368 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_334);
x_369 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_369, 0, x_334);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Nat_repr(x_44);
x_371 = l_Lean_numLitKind;
x_372 = l_Lean_Syntax_mkLit(x_371, x_370, x_359);
lean_inc(x_8);
x_373 = lean_array_push(x_8, x_372);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_359);
lean_ctor_set(x_374, 1, x_360);
lean_ctor_set(x_374, 2, x_373);
x_375 = lean_array_push(x_362, x_369);
x_376 = lean_array_push(x_375, x_374);
x_377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_377, 0, x_359);
lean_ctor_set(x_377, 1, x_367);
lean_ctor_set(x_377, 2, x_376);
lean_inc(x_8);
x_378 = lean_array_push(x_8, x_377);
x_379 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_379, 0, x_359);
lean_ctor_set(x_379, 1, x_360);
lean_ctor_set(x_379, 2, x_378);
x_380 = lean_array_push(x_362, x_365);
x_381 = lean_array_push(x_380, x_379);
x_382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_382, 0, x_359);
lean_ctor_set(x_382, 1, x_360);
lean_ctor_set(x_382, 2, x_381);
x_383 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_384 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_384, 0, x_334);
lean_ctor_set(x_384, 1, x_383);
x_385 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_386 = lean_array_push(x_385, x_345);
x_387 = lean_array_push(x_386, x_382);
x_388 = lean_array_push(x_387, x_384);
x_389 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_389, 0, x_359);
lean_ctor_set(x_389, 1, x_343);
lean_ctor_set(x_389, 2, x_388);
x_390 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_298, x_292, x_38, x_283, x_43, x_389, x_15, x_16, x_17, x_18, x_19, x_20, x_339);
lean_dec(x_24);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_25 = x_391;
x_26 = x_392;
goto block_33;
}
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_38);
x_393 = lean_nat_add(x_44, x_46);
x_394 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_45);
lean_ctor_set(x_394, 2, x_46);
x_395 = lean_ctor_get(x_39, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_39, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_39, 2);
lean_inc(x_397);
x_398 = lean_nat_dec_lt(x_396, x_397);
if (x_398 == 0)
{
lean_object* x_399; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_44);
lean_dec(x_24);
lean_ctor_set(x_34, 0, x_394);
x_399 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_399, 0, x_14);
x_25 = x_399;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_400 = x_39;
} else {
 lean_dec_ref(x_39);
 x_400 = lean_box(0);
}
x_401 = lean_array_fget(x_395, x_396);
x_402 = lean_unsigned_to_nat(1u);
x_403 = lean_nat_add(x_396, x_402);
lean_dec(x_396);
if (lean_is_scalar(x_400)) {
 x_404 = lean_alloc_ctor(0, 3, 0);
} else {
 x_404 = x_400;
}
lean_ctor_set(x_404, 0, x_395);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_404, 2, x_397);
x_405 = lean_ctor_get(x_42, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_42, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_42, 2);
lean_inc(x_407);
x_408 = lean_nat_dec_lt(x_406, x_407);
if (x_408 == 0)
{
lean_object* x_409; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_44);
lean_dec(x_24);
lean_ctor_set(x_34, 0, x_394);
lean_ctor_set(x_14, 0, x_404);
x_409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_409, 0, x_14);
x_25 = x_409;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
lean_free_object(x_37);
lean_free_object(x_14);
lean_free_object(x_34);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_410 = x_42;
} else {
 lean_dec_ref(x_42);
 x_410 = lean_box(0);
}
x_411 = lean_array_fget(x_405, x_406);
x_412 = lean_nat_add(x_406, x_402);
lean_dec(x_406);
if (lean_is_scalar(x_410)) {
 x_413 = lean_alloc_ctor(0, 3, 0);
} else {
 x_413 = x_410;
}
lean_ctor_set(x_413, 0, x_405);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set(x_413, 2, x_407);
lean_inc(x_6);
lean_inc(x_8);
x_414 = lean_array_push(x_8, x_6);
x_415 = lean_nat_sub(x_411, x_401);
lean_dec(x_401);
lean_dec(x_411);
x_416 = lean_nat_sub(x_415, x_402);
lean_dec(x_415);
x_417 = lean_unsigned_to_nat(0u);
lean_inc(x_416);
lean_inc(x_9);
x_418 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_416, x_417, x_416, x_402, x_414, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_416);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_nat_dec_lt(x_402, x_10);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_44);
lean_inc(x_19);
x_422 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_420);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_ctor_get(x_19, 8);
lean_inc(x_425);
x_426 = lean_st_ref_get(x_20, x_424);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_environment_main_module(x_429);
x_431 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_432 = lean_name_mk_string(x_7, x_431);
x_433 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_434 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_2);
lean_ctor_set(x_435, 2, x_434);
x_436 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_425);
lean_inc(x_430);
x_437 = l_Lean_addMacroScope(x_430, x_436, x_425);
x_438 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_5);
lean_inc(x_423);
x_440 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_440, 0, x_423);
lean_ctor_set(x_440, 1, x_435);
lean_ctor_set(x_440, 2, x_437);
lean_ctor_set(x_440, 3, x_439);
lean_inc(x_4);
x_441 = l_Lean_addMacroScope(x_430, x_4, x_425);
lean_inc(x_5);
lean_inc(x_3);
x_442 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_442, 0, x_423);
lean_ctor_set(x_442, 1, x_3);
lean_ctor_set(x_442, 2, x_441);
lean_ctor_set(x_442, 3, x_5);
lean_inc(x_8);
x_443 = lean_array_push(x_8, x_442);
x_444 = lean_box(2);
x_445 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_446 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set(x_446, 2, x_443);
x_447 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_448 = lean_array_push(x_447, x_440);
x_449 = lean_array_push(x_448, x_446);
x_450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_450, 0, x_444);
lean_ctor_set(x_450, 1, x_432);
lean_ctor_set(x_450, 2, x_449);
x_451 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_419, x_413, x_394, x_404, x_43, x_450, x_15, x_16, x_17, x_18, x_19, x_20, x_428);
lean_dec(x_24);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_25 = x_452;
x_26 = x_453;
goto block_33;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_inc(x_19);
x_454 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_420);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_ctor_get(x_19, 8);
lean_inc(x_457);
x_458 = lean_st_ref_get(x_20, x_456);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_environment_main_module(x_461);
x_463 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_464 = lean_name_mk_string(x_7, x_463);
x_465 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_455);
x_466 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_466, 0, x_455);
lean_ctor_set(x_466, 1, x_465);
x_467 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_468 = lean_name_mk_string(x_7, x_467);
x_469 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_470 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_471 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_2);
lean_ctor_set(x_471, 2, x_470);
x_472 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_457);
lean_inc(x_462);
x_473 = l_Lean_addMacroScope(x_462, x_472, x_457);
x_474 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_5);
lean_inc(x_455);
x_476 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_476, 0, x_455);
lean_ctor_set(x_476, 1, x_471);
lean_ctor_set(x_476, 2, x_473);
lean_ctor_set(x_476, 3, x_475);
lean_inc(x_4);
x_477 = l_Lean_addMacroScope(x_462, x_4, x_457);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_455);
x_478 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_478, 0, x_455);
lean_ctor_set(x_478, 1, x_3);
lean_ctor_set(x_478, 2, x_477);
lean_ctor_set(x_478, 3, x_5);
lean_inc(x_8);
x_479 = lean_array_push(x_8, x_478);
x_480 = lean_box(2);
x_481 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_482 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
lean_ctor_set(x_482, 2, x_479);
x_483 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_484 = lean_array_push(x_483, x_476);
x_485 = lean_array_push(x_484, x_482);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_480);
lean_ctor_set(x_486, 1, x_468);
lean_ctor_set(x_486, 2, x_485);
x_487 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_488 = lean_name_mk_string(x_7, x_487);
x_489 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_455);
x_490 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_490, 0, x_455);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Nat_repr(x_44);
x_492 = l_Lean_numLitKind;
x_493 = l_Lean_Syntax_mkLit(x_492, x_491, x_480);
lean_inc(x_8);
x_494 = lean_array_push(x_8, x_493);
x_495 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_495, 0, x_480);
lean_ctor_set(x_495, 1, x_481);
lean_ctor_set(x_495, 2, x_494);
x_496 = lean_array_push(x_483, x_490);
x_497 = lean_array_push(x_496, x_495);
x_498 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_498, 0, x_480);
lean_ctor_set(x_498, 1, x_488);
lean_ctor_set(x_498, 2, x_497);
lean_inc(x_8);
x_499 = lean_array_push(x_8, x_498);
x_500 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_500, 0, x_480);
lean_ctor_set(x_500, 1, x_481);
lean_ctor_set(x_500, 2, x_499);
x_501 = lean_array_push(x_483, x_486);
x_502 = lean_array_push(x_501, x_500);
x_503 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_503, 0, x_480);
lean_ctor_set(x_503, 1, x_481);
lean_ctor_set(x_503, 2, x_502);
x_504 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_505 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_505, 0, x_455);
lean_ctor_set(x_505, 1, x_504);
x_506 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_507 = lean_array_push(x_506, x_466);
x_508 = lean_array_push(x_507, x_503);
x_509 = lean_array_push(x_508, x_505);
x_510 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_510, 0, x_480);
lean_ctor_set(x_510, 1, x_464);
lean_ctor_set(x_510, 2, x_509);
x_511 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_419, x_413, x_394, x_404, x_43, x_510, x_15, x_16, x_17, x_18, x_19, x_20, x_460);
lean_dec(x_24);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_25 = x_512;
x_26 = x_513;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_514 = lean_ctor_get(x_37, 0);
x_515 = lean_ctor_get(x_37, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_37);
x_516 = lean_ctor_get(x_38, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_38, 1);
lean_inc(x_517);
x_518 = lean_ctor_get(x_38, 2);
lean_inc(x_518);
x_519 = lean_nat_dec_lt(x_516, x_517);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_24);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_514);
lean_ctor_set(x_520, 1, x_515);
lean_ctor_set(x_34, 1, x_520);
x_521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_521, 0, x_14);
x_25 = x_521;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_522 = x_38;
} else {
 lean_dec_ref(x_38);
 x_522 = lean_box(0);
}
x_523 = lean_nat_add(x_516, x_518);
if (lean_is_scalar(x_522)) {
 x_524 = lean_alloc_ctor(0, 3, 0);
} else {
 x_524 = x_522;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_517);
lean_ctor_set(x_524, 2, x_518);
x_525 = lean_ctor_get(x_39, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_39, 1);
lean_inc(x_526);
x_527 = lean_ctor_get(x_39, 2);
lean_inc(x_527);
x_528 = lean_nat_dec_lt(x_526, x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_516);
lean_dec(x_24);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_514);
lean_ctor_set(x_529, 1, x_515);
lean_ctor_set(x_34, 1, x_529);
lean_ctor_set(x_34, 0, x_524);
x_530 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_530, 0, x_14);
x_25 = x_530;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_531 = x_39;
} else {
 lean_dec_ref(x_39);
 x_531 = lean_box(0);
}
x_532 = lean_array_fget(x_525, x_526);
x_533 = lean_unsigned_to_nat(1u);
x_534 = lean_nat_add(x_526, x_533);
lean_dec(x_526);
if (lean_is_scalar(x_531)) {
 x_535 = lean_alloc_ctor(0, 3, 0);
} else {
 x_535 = x_531;
}
lean_ctor_set(x_535, 0, x_525);
lean_ctor_set(x_535, 1, x_534);
lean_ctor_set(x_535, 2, x_527);
x_536 = lean_ctor_get(x_514, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_514, 1);
lean_inc(x_537);
x_538 = lean_ctor_get(x_514, 2);
lean_inc(x_538);
x_539 = lean_nat_dec_lt(x_537, x_538);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_532);
lean_dec(x_516);
lean_dec(x_24);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_514);
lean_ctor_set(x_540, 1, x_515);
lean_ctor_set(x_34, 1, x_540);
lean_ctor_set(x_34, 0, x_524);
lean_ctor_set(x_14, 0, x_535);
x_541 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_541, 0, x_14);
x_25 = x_541;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
lean_free_object(x_14);
lean_free_object(x_34);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 lean_ctor_release(x_514, 2);
 x_542 = x_514;
} else {
 lean_dec_ref(x_514);
 x_542 = lean_box(0);
}
x_543 = lean_array_fget(x_536, x_537);
x_544 = lean_nat_add(x_537, x_533);
lean_dec(x_537);
if (lean_is_scalar(x_542)) {
 x_545 = lean_alloc_ctor(0, 3, 0);
} else {
 x_545 = x_542;
}
lean_ctor_set(x_545, 0, x_536);
lean_ctor_set(x_545, 1, x_544);
lean_ctor_set(x_545, 2, x_538);
lean_inc(x_6);
lean_inc(x_8);
x_546 = lean_array_push(x_8, x_6);
x_547 = lean_nat_sub(x_543, x_532);
lean_dec(x_532);
lean_dec(x_543);
x_548 = lean_nat_sub(x_547, x_533);
lean_dec(x_547);
x_549 = lean_unsigned_to_nat(0u);
lean_inc(x_548);
lean_inc(x_9);
x_550 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_548, x_549, x_548, x_533, x_546, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_548);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_nat_dec_lt(x_533, x_10);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_516);
lean_inc(x_19);
x_554 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_552);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_ctor_get(x_19, 8);
lean_inc(x_557);
x_558 = lean_st_ref_get(x_20, x_556);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_ctor_get(x_559, 0);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_environment_main_module(x_561);
x_563 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_564 = lean_name_mk_string(x_7, x_563);
x_565 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_566 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_567 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_2);
lean_ctor_set(x_567, 2, x_566);
x_568 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_557);
lean_inc(x_562);
x_569 = l_Lean_addMacroScope(x_562, x_568, x_557);
x_570 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_5);
lean_inc(x_555);
x_572 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_572, 0, x_555);
lean_ctor_set(x_572, 1, x_567);
lean_ctor_set(x_572, 2, x_569);
lean_ctor_set(x_572, 3, x_571);
lean_inc(x_4);
x_573 = l_Lean_addMacroScope(x_562, x_4, x_557);
lean_inc(x_5);
lean_inc(x_3);
x_574 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_574, 0, x_555);
lean_ctor_set(x_574, 1, x_3);
lean_ctor_set(x_574, 2, x_573);
lean_ctor_set(x_574, 3, x_5);
lean_inc(x_8);
x_575 = lean_array_push(x_8, x_574);
x_576 = lean_box(2);
x_577 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_578 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
lean_ctor_set(x_578, 2, x_575);
x_579 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_580 = lean_array_push(x_579, x_572);
x_581 = lean_array_push(x_580, x_578);
x_582 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_582, 0, x_576);
lean_ctor_set(x_582, 1, x_564);
lean_ctor_set(x_582, 2, x_581);
x_583 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_551, x_545, x_524, x_535, x_515, x_582, x_15, x_16, x_17, x_18, x_19, x_20, x_560);
lean_dec(x_24);
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
x_25 = x_584;
x_26 = x_585;
goto block_33;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_inc(x_19);
x_586 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_552);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_ctor_get(x_19, 8);
lean_inc(x_589);
x_590 = lean_st_ref_get(x_20, x_588);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_environment_main_module(x_593);
x_595 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_596 = lean_name_mk_string(x_7, x_595);
x_597 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_587);
x_598 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_598, 0, x_587);
lean_ctor_set(x_598, 1, x_597);
x_599 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_600 = lean_name_mk_string(x_7, x_599);
x_601 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_602 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_603 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_2);
lean_ctor_set(x_603, 2, x_602);
x_604 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_589);
lean_inc(x_594);
x_605 = l_Lean_addMacroScope(x_594, x_604, x_589);
x_606 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_5);
lean_inc(x_587);
x_608 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_608, 0, x_587);
lean_ctor_set(x_608, 1, x_603);
lean_ctor_set(x_608, 2, x_605);
lean_ctor_set(x_608, 3, x_607);
lean_inc(x_4);
x_609 = l_Lean_addMacroScope(x_594, x_4, x_589);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_587);
x_610 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_610, 0, x_587);
lean_ctor_set(x_610, 1, x_3);
lean_ctor_set(x_610, 2, x_609);
lean_ctor_set(x_610, 3, x_5);
lean_inc(x_8);
x_611 = lean_array_push(x_8, x_610);
x_612 = lean_box(2);
x_613 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_614 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
lean_ctor_set(x_614, 2, x_611);
x_615 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_616 = lean_array_push(x_615, x_608);
x_617 = lean_array_push(x_616, x_614);
x_618 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_618, 0, x_612);
lean_ctor_set(x_618, 1, x_600);
lean_ctor_set(x_618, 2, x_617);
x_619 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_620 = lean_name_mk_string(x_7, x_619);
x_621 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_587);
x_622 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_622, 0, x_587);
lean_ctor_set(x_622, 1, x_621);
x_623 = l_Nat_repr(x_516);
x_624 = l_Lean_numLitKind;
x_625 = l_Lean_Syntax_mkLit(x_624, x_623, x_612);
lean_inc(x_8);
x_626 = lean_array_push(x_8, x_625);
x_627 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_627, 0, x_612);
lean_ctor_set(x_627, 1, x_613);
lean_ctor_set(x_627, 2, x_626);
x_628 = lean_array_push(x_615, x_622);
x_629 = lean_array_push(x_628, x_627);
x_630 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_630, 0, x_612);
lean_ctor_set(x_630, 1, x_620);
lean_ctor_set(x_630, 2, x_629);
lean_inc(x_8);
x_631 = lean_array_push(x_8, x_630);
x_632 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_632, 0, x_612);
lean_ctor_set(x_632, 1, x_613);
lean_ctor_set(x_632, 2, x_631);
x_633 = lean_array_push(x_615, x_618);
x_634 = lean_array_push(x_633, x_632);
x_635 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_635, 0, x_612);
lean_ctor_set(x_635, 1, x_613);
lean_ctor_set(x_635, 2, x_634);
x_636 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_637 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_637, 0, x_587);
lean_ctor_set(x_637, 1, x_636);
x_638 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_639 = lean_array_push(x_638, x_598);
x_640 = lean_array_push(x_639, x_635);
x_641 = lean_array_push(x_640, x_637);
x_642 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_642, 0, x_612);
lean_ctor_set(x_642, 1, x_596);
lean_ctor_set(x_642, 2, x_641);
x_643 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_551, x_545, x_524, x_535, x_515, x_642, x_15, x_16, x_17, x_18, x_19, x_20, x_592);
lean_dec(x_24);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_25 = x_644;
x_26 = x_645;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_646 = lean_ctor_get(x_34, 1);
x_647 = lean_ctor_get(x_34, 0);
x_648 = lean_ctor_get(x_14, 0);
lean_inc(x_648);
lean_dec(x_14);
x_649 = lean_ctor_get(x_646, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_646, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_651 = x_646;
} else {
 lean_dec_ref(x_646);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_647, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_647, 1);
lean_inc(x_653);
x_654 = lean_ctor_get(x_647, 2);
lean_inc(x_654);
x_655 = lean_nat_dec_lt(x_652, x_653);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_24);
if (lean_is_scalar(x_651)) {
 x_656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_656 = x_651;
}
lean_ctor_set(x_656, 0, x_649);
lean_ctor_set(x_656, 1, x_650);
lean_ctor_set(x_34, 1, x_656);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_648);
lean_ctor_set(x_657, 1, x_34);
x_658 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_658, 0, x_657);
x_25 = x_658;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 lean_ctor_release(x_647, 2);
 x_659 = x_647;
} else {
 lean_dec_ref(x_647);
 x_659 = lean_box(0);
}
x_660 = lean_nat_add(x_652, x_654);
if (lean_is_scalar(x_659)) {
 x_661 = lean_alloc_ctor(0, 3, 0);
} else {
 x_661 = x_659;
}
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_653);
lean_ctor_set(x_661, 2, x_654);
x_662 = lean_ctor_get(x_648, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_648, 1);
lean_inc(x_663);
x_664 = lean_ctor_get(x_648, 2);
lean_inc(x_664);
x_665 = lean_nat_dec_lt(x_663, x_664);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_652);
lean_dec(x_24);
if (lean_is_scalar(x_651)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_651;
}
lean_ctor_set(x_666, 0, x_649);
lean_ctor_set(x_666, 1, x_650);
lean_ctor_set(x_34, 1, x_666);
lean_ctor_set(x_34, 0, x_661);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_648);
lean_ctor_set(x_667, 1, x_34);
x_668 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_668, 0, x_667);
x_25 = x_668;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 lean_ctor_release(x_648, 2);
 x_669 = x_648;
} else {
 lean_dec_ref(x_648);
 x_669 = lean_box(0);
}
x_670 = lean_array_fget(x_662, x_663);
x_671 = lean_unsigned_to_nat(1u);
x_672 = lean_nat_add(x_663, x_671);
lean_dec(x_663);
if (lean_is_scalar(x_669)) {
 x_673 = lean_alloc_ctor(0, 3, 0);
} else {
 x_673 = x_669;
}
lean_ctor_set(x_673, 0, x_662);
lean_ctor_set(x_673, 1, x_672);
lean_ctor_set(x_673, 2, x_664);
x_674 = lean_ctor_get(x_649, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_649, 1);
lean_inc(x_675);
x_676 = lean_ctor_get(x_649, 2);
lean_inc(x_676);
x_677 = lean_nat_dec_lt(x_675, x_676);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_676);
lean_dec(x_675);
lean_dec(x_674);
lean_dec(x_670);
lean_dec(x_652);
lean_dec(x_24);
if (lean_is_scalar(x_651)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_651;
}
lean_ctor_set(x_678, 0, x_649);
lean_ctor_set(x_678, 1, x_650);
lean_ctor_set(x_34, 1, x_678);
lean_ctor_set(x_34, 0, x_661);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_673);
lean_ctor_set(x_679, 1, x_34);
x_680 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_25 = x_680;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
lean_dec(x_651);
lean_free_object(x_34);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 lean_ctor_release(x_649, 2);
 x_681 = x_649;
} else {
 lean_dec_ref(x_649);
 x_681 = lean_box(0);
}
x_682 = lean_array_fget(x_674, x_675);
x_683 = lean_nat_add(x_675, x_671);
lean_dec(x_675);
if (lean_is_scalar(x_681)) {
 x_684 = lean_alloc_ctor(0, 3, 0);
} else {
 x_684 = x_681;
}
lean_ctor_set(x_684, 0, x_674);
lean_ctor_set(x_684, 1, x_683);
lean_ctor_set(x_684, 2, x_676);
lean_inc(x_6);
lean_inc(x_8);
x_685 = lean_array_push(x_8, x_6);
x_686 = lean_nat_sub(x_682, x_670);
lean_dec(x_670);
lean_dec(x_682);
x_687 = lean_nat_sub(x_686, x_671);
lean_dec(x_686);
x_688 = lean_unsigned_to_nat(0u);
lean_inc(x_687);
lean_inc(x_9);
x_689 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_687, x_688, x_687, x_671, x_685, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_687);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_nat_dec_lt(x_671, x_10);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_652);
lean_inc(x_19);
x_693 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_691);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_ctor_get(x_19, 8);
lean_inc(x_696);
x_697 = lean_st_ref_get(x_20, x_695);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec(x_697);
x_700 = lean_ctor_get(x_698, 0);
lean_inc(x_700);
lean_dec(x_698);
x_701 = lean_environment_main_module(x_700);
x_702 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_703 = lean_name_mk_string(x_7, x_702);
x_704 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_705 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_706 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_2);
lean_ctor_set(x_706, 2, x_705);
x_707 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_696);
lean_inc(x_701);
x_708 = l_Lean_addMacroScope(x_701, x_707, x_696);
x_709 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_5);
lean_inc(x_694);
x_711 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_711, 0, x_694);
lean_ctor_set(x_711, 1, x_706);
lean_ctor_set(x_711, 2, x_708);
lean_ctor_set(x_711, 3, x_710);
lean_inc(x_4);
x_712 = l_Lean_addMacroScope(x_701, x_4, x_696);
lean_inc(x_5);
lean_inc(x_3);
x_713 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_713, 0, x_694);
lean_ctor_set(x_713, 1, x_3);
lean_ctor_set(x_713, 2, x_712);
lean_ctor_set(x_713, 3, x_5);
lean_inc(x_8);
x_714 = lean_array_push(x_8, x_713);
x_715 = lean_box(2);
x_716 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_717 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
lean_ctor_set(x_717, 2, x_714);
x_718 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_719 = lean_array_push(x_718, x_711);
x_720 = lean_array_push(x_719, x_717);
x_721 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_721, 0, x_715);
lean_ctor_set(x_721, 1, x_703);
lean_ctor_set(x_721, 2, x_720);
x_722 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_690, x_684, x_661, x_673, x_650, x_721, x_15, x_16, x_17, x_18, x_19, x_20, x_699);
lean_dec(x_24);
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_25 = x_723;
x_26 = x_724;
goto block_33;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_inc(x_19);
x_725 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_691);
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec(x_725);
x_728 = lean_ctor_get(x_19, 8);
lean_inc(x_728);
x_729 = lean_st_ref_get(x_20, x_727);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = lean_ctor_get(x_730, 0);
lean_inc(x_732);
lean_dec(x_730);
x_733 = lean_environment_main_module(x_732);
x_734 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_735 = lean_name_mk_string(x_7, x_734);
x_736 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_726);
x_737 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_737, 0, x_726);
lean_ctor_set(x_737, 1, x_736);
x_738 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_739 = lean_name_mk_string(x_7, x_738);
x_740 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_741 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_742 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_2);
lean_ctor_set(x_742, 2, x_741);
x_743 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_728);
lean_inc(x_733);
x_744 = l_Lean_addMacroScope(x_733, x_743, x_728);
x_745 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_5);
lean_inc(x_726);
x_747 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_747, 0, x_726);
lean_ctor_set(x_747, 1, x_742);
lean_ctor_set(x_747, 2, x_744);
lean_ctor_set(x_747, 3, x_746);
lean_inc(x_4);
x_748 = l_Lean_addMacroScope(x_733, x_4, x_728);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_726);
x_749 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_749, 0, x_726);
lean_ctor_set(x_749, 1, x_3);
lean_ctor_set(x_749, 2, x_748);
lean_ctor_set(x_749, 3, x_5);
lean_inc(x_8);
x_750 = lean_array_push(x_8, x_749);
x_751 = lean_box(2);
x_752 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_753 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
lean_ctor_set(x_753, 2, x_750);
x_754 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_755 = lean_array_push(x_754, x_747);
x_756 = lean_array_push(x_755, x_753);
x_757 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_757, 0, x_751);
lean_ctor_set(x_757, 1, x_739);
lean_ctor_set(x_757, 2, x_756);
x_758 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_759 = lean_name_mk_string(x_7, x_758);
x_760 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_726);
x_761 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_761, 0, x_726);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Nat_repr(x_652);
x_763 = l_Lean_numLitKind;
x_764 = l_Lean_Syntax_mkLit(x_763, x_762, x_751);
lean_inc(x_8);
x_765 = lean_array_push(x_8, x_764);
x_766 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_766, 0, x_751);
lean_ctor_set(x_766, 1, x_752);
lean_ctor_set(x_766, 2, x_765);
x_767 = lean_array_push(x_754, x_761);
x_768 = lean_array_push(x_767, x_766);
x_769 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_769, 0, x_751);
lean_ctor_set(x_769, 1, x_759);
lean_ctor_set(x_769, 2, x_768);
lean_inc(x_8);
x_770 = lean_array_push(x_8, x_769);
x_771 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_771, 0, x_751);
lean_ctor_set(x_771, 1, x_752);
lean_ctor_set(x_771, 2, x_770);
x_772 = lean_array_push(x_754, x_757);
x_773 = lean_array_push(x_772, x_771);
x_774 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_774, 0, x_751);
lean_ctor_set(x_774, 1, x_752);
lean_ctor_set(x_774, 2, x_773);
x_775 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_776 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_776, 0, x_726);
lean_ctor_set(x_776, 1, x_775);
x_777 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_778 = lean_array_push(x_777, x_737);
x_779 = lean_array_push(x_778, x_774);
x_780 = lean_array_push(x_779, x_776);
x_781 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_781, 0, x_751);
lean_ctor_set(x_781, 1, x_735);
lean_ctor_set(x_781, 2, x_780);
x_782 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_690, x_684, x_661, x_673, x_650, x_781, x_15, x_16, x_17, x_18, x_19, x_20, x_731);
lean_dec(x_24);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
x_25 = x_783;
x_26 = x_784;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_785 = lean_ctor_get(x_34, 1);
x_786 = lean_ctor_get(x_34, 0);
lean_inc(x_785);
lean_inc(x_786);
lean_dec(x_34);
x_787 = lean_ctor_get(x_14, 0);
lean_inc(x_787);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_788 = x_14;
} else {
 lean_dec_ref(x_14);
 x_788 = lean_box(0);
}
x_789 = lean_ctor_get(x_785, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_785, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_791 = x_785;
} else {
 lean_dec_ref(x_785);
 x_791 = lean_box(0);
}
x_792 = lean_ctor_get(x_786, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_786, 1);
lean_inc(x_793);
x_794 = lean_ctor_get(x_786, 2);
lean_inc(x_794);
x_795 = lean_nat_dec_lt(x_792, x_793);
if (x_795 == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_794);
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_24);
if (lean_is_scalar(x_791)) {
 x_796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_796 = x_791;
}
lean_ctor_set(x_796, 0, x_789);
lean_ctor_set(x_796, 1, x_790);
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_786);
lean_ctor_set(x_797, 1, x_796);
if (lean_is_scalar(x_788)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_788;
}
lean_ctor_set(x_798, 0, x_787);
lean_ctor_set(x_798, 1, x_797);
x_799 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_799, 0, x_798);
x_25 = x_799;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 x_800 = x_786;
} else {
 lean_dec_ref(x_786);
 x_800 = lean_box(0);
}
x_801 = lean_nat_add(x_792, x_794);
if (lean_is_scalar(x_800)) {
 x_802 = lean_alloc_ctor(0, 3, 0);
} else {
 x_802 = x_800;
}
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_793);
lean_ctor_set(x_802, 2, x_794);
x_803 = lean_ctor_get(x_787, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_787, 1);
lean_inc(x_804);
x_805 = lean_ctor_get(x_787, 2);
lean_inc(x_805);
x_806 = lean_nat_dec_lt(x_804, x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_805);
lean_dec(x_804);
lean_dec(x_803);
lean_dec(x_792);
lean_dec(x_24);
if (lean_is_scalar(x_791)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_791;
}
lean_ctor_set(x_807, 0, x_789);
lean_ctor_set(x_807, 1, x_790);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_802);
lean_ctor_set(x_808, 1, x_807);
if (lean_is_scalar(x_788)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_788;
}
lean_ctor_set(x_809, 0, x_787);
lean_ctor_set(x_809, 1, x_808);
x_810 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_810, 0, x_809);
x_25 = x_810;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; 
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 lean_ctor_release(x_787, 2);
 x_811 = x_787;
} else {
 lean_dec_ref(x_787);
 x_811 = lean_box(0);
}
x_812 = lean_array_fget(x_803, x_804);
x_813 = lean_unsigned_to_nat(1u);
x_814 = lean_nat_add(x_804, x_813);
lean_dec(x_804);
if (lean_is_scalar(x_811)) {
 x_815 = lean_alloc_ctor(0, 3, 0);
} else {
 x_815 = x_811;
}
lean_ctor_set(x_815, 0, x_803);
lean_ctor_set(x_815, 1, x_814);
lean_ctor_set(x_815, 2, x_805);
x_816 = lean_ctor_get(x_789, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_789, 1);
lean_inc(x_817);
x_818 = lean_ctor_get(x_789, 2);
lean_inc(x_818);
x_819 = lean_nat_dec_lt(x_817, x_818);
if (x_819 == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_818);
lean_dec(x_817);
lean_dec(x_816);
lean_dec(x_812);
lean_dec(x_792);
lean_dec(x_24);
if (lean_is_scalar(x_791)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_791;
}
lean_ctor_set(x_820, 0, x_789);
lean_ctor_set(x_820, 1, x_790);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_802);
lean_ctor_set(x_821, 1, x_820);
if (lean_is_scalar(x_788)) {
 x_822 = lean_alloc_ctor(0, 2, 0);
} else {
 x_822 = x_788;
}
lean_ctor_set(x_822, 0, x_815);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_823, 0, x_822);
x_25 = x_823;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; 
lean_dec(x_791);
lean_dec(x_788);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 lean_ctor_release(x_789, 2);
 x_824 = x_789;
} else {
 lean_dec_ref(x_789);
 x_824 = lean_box(0);
}
x_825 = lean_array_fget(x_816, x_817);
x_826 = lean_nat_add(x_817, x_813);
lean_dec(x_817);
if (lean_is_scalar(x_824)) {
 x_827 = lean_alloc_ctor(0, 3, 0);
} else {
 x_827 = x_824;
}
lean_ctor_set(x_827, 0, x_816);
lean_ctor_set(x_827, 1, x_826);
lean_ctor_set(x_827, 2, x_818);
lean_inc(x_6);
lean_inc(x_8);
x_828 = lean_array_push(x_8, x_6);
x_829 = lean_nat_sub(x_825, x_812);
lean_dec(x_812);
lean_dec(x_825);
x_830 = lean_nat_sub(x_829, x_813);
lean_dec(x_829);
x_831 = lean_unsigned_to_nat(0u);
lean_inc(x_830);
lean_inc(x_9);
x_832 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_830, x_831, x_830, x_813, x_828, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_830);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_nat_dec_lt(x_813, x_10);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_792);
lean_inc(x_19);
x_836 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_834);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = lean_ctor_get(x_19, 8);
lean_inc(x_839);
x_840 = lean_st_ref_get(x_20, x_838);
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec(x_840);
x_843 = lean_ctor_get(x_841, 0);
lean_inc(x_843);
lean_dec(x_841);
x_844 = lean_environment_main_module(x_843);
x_845 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_846 = lean_name_mk_string(x_7, x_845);
x_847 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_848 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_849 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_2);
lean_ctor_set(x_849, 2, x_848);
x_850 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_839);
lean_inc(x_844);
x_851 = l_Lean_addMacroScope(x_844, x_850, x_839);
x_852 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_5);
lean_inc(x_837);
x_854 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_854, 0, x_837);
lean_ctor_set(x_854, 1, x_849);
lean_ctor_set(x_854, 2, x_851);
lean_ctor_set(x_854, 3, x_853);
lean_inc(x_4);
x_855 = l_Lean_addMacroScope(x_844, x_4, x_839);
lean_inc(x_5);
lean_inc(x_3);
x_856 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_856, 0, x_837);
lean_ctor_set(x_856, 1, x_3);
lean_ctor_set(x_856, 2, x_855);
lean_ctor_set(x_856, 3, x_5);
lean_inc(x_8);
x_857 = lean_array_push(x_8, x_856);
x_858 = lean_box(2);
x_859 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_860 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
lean_ctor_set(x_860, 2, x_857);
x_861 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_862 = lean_array_push(x_861, x_854);
x_863 = lean_array_push(x_862, x_860);
x_864 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_864, 0, x_858);
lean_ctor_set(x_864, 1, x_846);
lean_ctor_set(x_864, 2, x_863);
x_865 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_833, x_827, x_802, x_815, x_790, x_864, x_15, x_16, x_17, x_18, x_19, x_20, x_842);
lean_dec(x_24);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_25 = x_866;
x_26 = x_867;
goto block_33;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_inc(x_19);
x_868 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_834);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_19, 8);
lean_inc(x_871);
x_872 = lean_st_ref_get(x_20, x_870);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 0);
lean_inc(x_875);
lean_dec(x_873);
x_876 = lean_environment_main_module(x_875);
x_877 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_878 = lean_name_mk_string(x_7, x_877);
x_879 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_869);
x_880 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_880, 0, x_869);
lean_ctor_set(x_880, 1, x_879);
x_881 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_882 = lean_name_mk_string(x_7, x_881);
x_883 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_884 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_885 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_885, 0, x_883);
lean_ctor_set(x_885, 1, x_2);
lean_ctor_set(x_885, 2, x_884);
x_886 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_871);
lean_inc(x_876);
x_887 = l_Lean_addMacroScope(x_876, x_886, x_871);
x_888 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_5);
lean_inc(x_869);
x_890 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_890, 0, x_869);
lean_ctor_set(x_890, 1, x_885);
lean_ctor_set(x_890, 2, x_887);
lean_ctor_set(x_890, 3, x_889);
lean_inc(x_4);
x_891 = l_Lean_addMacroScope(x_876, x_4, x_871);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_869);
x_892 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_892, 0, x_869);
lean_ctor_set(x_892, 1, x_3);
lean_ctor_set(x_892, 2, x_891);
lean_ctor_set(x_892, 3, x_5);
lean_inc(x_8);
x_893 = lean_array_push(x_8, x_892);
x_894 = lean_box(2);
x_895 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_896 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
lean_ctor_set(x_896, 2, x_893);
x_897 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_898 = lean_array_push(x_897, x_890);
x_899 = lean_array_push(x_898, x_896);
x_900 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_900, 0, x_894);
lean_ctor_set(x_900, 1, x_882);
lean_ctor_set(x_900, 2, x_899);
x_901 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_902 = lean_name_mk_string(x_7, x_901);
x_903 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_869);
x_904 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_904, 0, x_869);
lean_ctor_set(x_904, 1, x_903);
x_905 = l_Nat_repr(x_792);
x_906 = l_Lean_numLitKind;
x_907 = l_Lean_Syntax_mkLit(x_906, x_905, x_894);
lean_inc(x_8);
x_908 = lean_array_push(x_8, x_907);
x_909 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_909, 0, x_894);
lean_ctor_set(x_909, 1, x_895);
lean_ctor_set(x_909, 2, x_908);
x_910 = lean_array_push(x_897, x_904);
x_911 = lean_array_push(x_910, x_909);
x_912 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_912, 0, x_894);
lean_ctor_set(x_912, 1, x_902);
lean_ctor_set(x_912, 2, x_911);
lean_inc(x_8);
x_913 = lean_array_push(x_8, x_912);
x_914 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_914, 0, x_894);
lean_ctor_set(x_914, 1, x_895);
lean_ctor_set(x_914, 2, x_913);
x_915 = lean_array_push(x_897, x_900);
x_916 = lean_array_push(x_915, x_914);
x_917 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_917, 0, x_894);
lean_ctor_set(x_917, 1, x_895);
lean_ctor_set(x_917, 2, x_916);
x_918 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_919 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_919, 0, x_869);
lean_ctor_set(x_919, 1, x_918);
x_920 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_921 = lean_array_push(x_920, x_880);
x_922 = lean_array_push(x_921, x_917);
x_923 = lean_array_push(x_922, x_919);
x_924 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_924, 0, x_894);
lean_ctor_set(x_924, 1, x_878);
lean_ctor_set(x_924, 2, x_923);
x_925 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_833, x_827, x_802, x_815, x_790, x_924, x_15, x_16, x_17, x_18, x_19, x_20, x_874);
lean_dec(x_24);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
x_25 = x_926;
x_26 = x_927;
goto block_33;
}
}
}
}
}
block_33:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = 1;
x_31 = lean_usize_add(x_13, x_30);
x_13 = x_31;
x_14 = x_29;
x_21 = x_26;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_8);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 8);
lean_inc(x_14);
x_15 = lean_st_ref_get(x_9, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_environment_main_module(x_18);
x_20 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
x_21 = l_Lean_addMacroScope(x_19, x_20, x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_inc(x_8);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = lean_box(2);
x_35 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_array_get_size(x_2);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_toSubarray___rarg(x_2, x_38, x_37);
x_40 = lean_array_get_size(x_3);
x_41 = l_Array_toSubarray___rarg(x_3, x_38, x_40);
x_42 = lean_array_get_size(x_1);
x_43 = lean_unsigned_to_nat(1u);
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_usize_of_nat(x_42);
x_50 = 0;
x_51 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_1, x_38, x_23, x_20, x_22, x_24, x_51, x_32, x_36, x_42, x_1, x_49, x_50, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_42);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_23 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 0;
x_22 = l_Lean_Elab_Term_SavedState_restore(x_10, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Elab_Term_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 0;
x_27 = l_Lean_Elab_Term_SavedState_restore(x_15, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_10, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_21 = lean_array_uget(x_8, x_10);
lean_inc(x_16);
lean_inc(x_6);
x_22 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_6, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = lean_usize_add(x_10, x_28);
lean_inc(x_7);
{
size_t _tmp_9 = x_29;
lean_object* _tmp_10 = x_7;
lean_object* _tmp_17 = x_27;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_18 = _tmp_17;
}
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_42 = x_26;
} else {
 lean_dec_ref(x_26);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed), 18, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to prove termination, use `termination_by` to specify a well-founded relation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_13 = l_Lean_Elab_WF_getNumCandidateArgs(x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_3, x_17, x_18, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
x_23 = lean_unsigned_to_nat(32u);
x_24 = l_Lean_Elab_WF_generateCombinations_x3f(x_20, x_14, x_23);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_14, x_28, x_25, x_27, x_18, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = lean_apply_8(x_22, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
x_16 = l_Lean_Meta_instantiateMVars(x_14, x_6, x_7, x_8, x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_17);
x_19 = l_Lean_Meta_getMVars(x_17, x_6, x_7, x_8, x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_20, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_8(x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel_guess___rarg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_1, 0, x_6);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_box(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_5);
x_25 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_1);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_6);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_box(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_35, 0, x_29);
lean_closure_set(x_35, 1, x_30);
lean_closure_set(x_35, 2, x_33);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_31);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_31);
lean_closure_set(x_36, 2, x_5);
x_37 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WellFoundedRelation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabWFRel start: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_Meta_getLevel(x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkApp(x_20, x_4);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_43 = lean_st_ref_get(x_12, x_16);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_23 = x_48;
x_24 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_23 = x_53;
x_24 = x_52;
goto block_42;
}
block_42:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = 0;
x_28 = lean_box(0);
lean_inc(x_9);
x_29 = l_Lean_Meta_mkFreshTypeMVar(x_27, x_28, x_9, x_10, x_11, x_12, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_22, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_39);
return x_41;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1);
l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4);
l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1 = _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__1);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__2);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__3);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__4);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__5 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__5);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__6 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__6);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__7 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__7);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__8 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__8);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__9 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__9);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__10 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__10);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__11 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__11);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__12 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__12);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__13 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__13);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___closed__2 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___closed__3 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__3);
l_Lean_Elab_WF_elabWFRel___rarg___closed__4 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
