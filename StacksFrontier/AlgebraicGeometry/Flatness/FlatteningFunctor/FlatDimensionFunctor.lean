module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BaseChangeTransition
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The functor of flatness in dimensions at least `n`

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `n` be a natural number. For a scheme `T` over `S` write
`X_T = X ×_S T` and let `F_T` be the pullback of `F` along the projection `X_T ⟶ X`. The
morphism `X_T ⟶ T` is again locally of finite type and `F_T` is again a quasi-coherent module
of finite type, so it makes sense to ask whether `F_T` is flat over `T` in dimensions `≥ n`.
That condition is stable under a further base change, hence defines a subterminal set-valued
functor `F_n` on schemes over `S`.

## Main definitions

* `AlgebraicGeometry.FlatDimensionSituation`: the standing morphism, module and dimension bound.
* `AlgebraicGeometry.FlatDimensionSituation.baseChangeMap` and
  `AlgebraicGeometry.FlatDimensionSituation.baseChangeModule`: the base-changed morphism
  `X_T ⟶ T` and the base-changed module `F_T`.
* `AlgebraicGeometry.FlatDimensionSituation.baseChangeModuleIso`: the comparison isomorphism
  identifying the iterated base change `(F_T)_{T'}` along the transition morphism with `F_{T'}`.
* `AlgebraicGeometry.FlatDimensionSituation.IsFlatInDimensionsGEAfterBaseChange`: the
  condition that `F_T` is flat over `T` in dimensions `≥ n`.
* `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor`: the functor `F_n`.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.baseChangeMap_locallyOfFiniteType`: `X_T ⟶ T` is
  locally of finite type.
* `AlgebraicGeometry.FlatDimensionSituation.baseChangeModule_isFiniteType`: `F_T` is of
  finite type.
* `AlgebraicGeometry.IsFlatOverInDimensionsGE.of_moduleIso`: flatness over the base in
  dimensions `≥ n` depends only on the isomorphism class of the module.
* `AlgebraicGeometry.FlatDimensionSituation.isFlatInDimensionsGEAfterBaseChange_of_hom`: the
  condition is inherited along a morphism of schemes over `S`.
* `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_obj_nonempty_iff`: a value of
  `F_n` is nonempty exactly when the corresponding base change is flat in dimensions `≥ n`.

## References

* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
* [Stacks Project, Tag 01T4](https://stacks.math.columbia.edu/tag/01T4)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness over the base in dimensions `≥ n` depends only on the isomorphism class of the
module. -/
public theorem IsFlatOverInDimensionsGE.of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {F G : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    [G.IsQuasicoherent] [G.IsFiniteType] (e : F ≅ G) {n : ℕ}
    (hF : IsFlatOverInDimensionsGE f F n) : IsFlatOverInDimensionsGE f G n := by
  rw [isFlatOverInDimensionsGE_iff_forall_topologicalKrullDim_lt] at hF ⊢
  intro s
  have hset : {y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom G (f.fiberι s y)} =
      {y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} :=
    Set.ext fun y =>
      not_congr (isFlatOverAt_iff_of_moduleIso f.toLRSHom.toShHom e (f.fiberι s y)).symm
  exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.setCongr hset)
    (Homeomorph.setCongr hset).isHomeomorph).trans_lt (hF s)

/-- A morphism of schemes `f : X ⟶ S` locally of finite type together with a quasi-coherent
module `F` of finite type on `X` and a bound `n` on fibre dimensions. -/
@[stacks 05MT "the situation"]
public structure FlatDimensionSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The total space. -/
  X : Scheme.{u}
  /-- The morphism whose base changes are tested. -/
  f : X ⟶ S
  /-- The morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType f]
  /-- The module on the total space. -/
  F : X.Modules
  /-- The module is quasi-coherent. -/
  [isQuasicoherent : F.IsQuasicoherent]
  /-- The module is of finite type. -/
  [isFiniteType : F.IsFiniteType]
  /-- The bound below which failure of flatness is allowed in the fibres. -/
  n : ℕ

namespace FlatDimensionSituation

attribute [instance] locallyOfFiniteType isQuasicoherent isFiniteType

/-- The base-changed morphism `X_T = X ×_S T ⟶ T`. -/
@[stacks 05MT "the base-changed morphism"]
public noncomputable abbrev baseChangeMap (D : FlatDimensionSituation.{u}) (T : Over D.S) :
    pullback D.f T.hom ⟶ T.left :=
  pullback.snd D.f T.hom

/-- The base change `F_T` of the module, i.e. its pullback along the projection
`X_T = X ×_S T ⟶ X`. -/
@[stacks 05MT "the base-changed module"]
public noncomputable abbrev baseChangeModule (D : FlatDimensionSituation.{u}) (T : Over D.S) :
    (pullback D.f T.hom).Modules :=
  (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F

/-- The base-changed morphism `X_T ⟶ T` is again locally of finite type. -/
@[stacks 05MT "X_T → T is of finite type"]
public instance baseChangeMap_locallyOfFiniteType (D : FlatDimensionSituation.{u})
    (T : Over D.S) : LocallyOfFiniteType (D.baseChangeMap T) :=
  locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback D.f T.hom) D.locallyOfFiniteType

/-- The base-changed module `F_T` is again of finite type. -/
@[stacks 05MT "F_T is of finite type"]
public noncomputable instance baseChangeModule_isFiniteType (D : FlatDimensionSituation.{u})
    (T : Over D.S) : (D.baseChangeModule T).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType (pullback.fst D.f T.hom).toLRSHom.toShHom D.F

/-- The base-changed module `F_T` is again quasi-coherent. -/
public instance baseChangeModule_isQuasicoherent (D : FlatDimensionSituation.{u})
    (T : Over D.S) : (D.baseChangeModule T).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _
    (pullback.fst D.f T.hom).toLRSHom.toShHom D.F D.isQuasicoherent

/-- The base-changed module `F_T` is flat over `T` in dimensions `≥ n`. -/
@[stacks 05MT "the condition tested by the functor"]
public noncomputable abbrev IsFlatInDimensionsGEAfterBaseChange
    (D : FlatDimensionSituation.{u}) (T : Over D.S) : Prop :=
  IsFlatOverInDimensionsGE (D.baseChangeMap T) (D.baseChangeModule T) D.n

/-- The iterated base change `(F_T)_{T'}` of the module along the transition morphism
`X_{T'} ⟶ X_T` is canonically isomorphic to the base change `F_{T'}`. -/
public noncomputable def baseChangeModuleIso (D : FlatDimensionSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) :
    (Scheme.Modules.pullback (Stacks.BaseChange.transition D.f g)).obj
        (D.baseChangeModule T) ≅ D.baseChangeModule T' :=
  (Scheme.Modules.pullbackComp (Stacks.BaseChange.transition D.f g)
      (pullback.fst D.f T.hom)).app D.F ≪≫
    (Scheme.Modules.pullbackCongr (Stacks.BaseChange.transition_comp_fst D.f g)).app D.F

/-- Flatness of the base-changed module in dimensions `≥ n` is inherited along a morphism
`T' ⟶ T` of schemes over `S`. -/
@[stacks 05MT "base-change stability of the condition"]
public theorem isFlatInDimensionsGEAfterBaseChange_of_hom (D : FlatDimensionSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) (h : D.IsFlatInDimensionsGEAfterBaseChange T) :
    D.IsFlatInDimensionsGEAfterBaseChange T' :=
  IsFlatOverInDimensionsGE.of_moduleIso (D.baseChangeMap T') (D.baseChangeModuleIso g)
    (IsFlatOverInDimensionsGE.of_isPullback
      (Stacks.BaseChange.transition_isPullback D.f g) (D.baseChangeModule T) D.n h)

/-- The functor `F_n : (Sch/S)ᵒᵖ ⥤ Sets` sending a scheme `T` over `S` to a singleton if `F_T`
is flat over `T` in dimensions `≥ n`, and to the empty set otherwise. -/
@[stacks 05MT "the functor F_n"]
public noncomputable def flatDimensionFunctor (D : FlatDimensionSituation.{u}) :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsFlatInDimensionsGEAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isFlatInDimensionsGEAfterBaseChange_of_hom g.unop h.down⟩
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- The functor `F_n` sends a scheme over `S` to the lifted flatness condition. -/
@[simp] public theorem flatDimensionFunctor_obj (D : FlatDimensionSituation.{u})
    (T : Over D.S) :
    D.flatDimensionFunctor.obj (Opposite.op T) =
      PLift (D.IsFlatInDimensionsGEAfterBaseChange T) := rfl

/-- The restriction maps of `F_n` are induced by base-change stability of the condition. -/
@[simp] public theorem flatDimensionFunctor_map (D : FlatDimensionSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T)
    (h : PLift (D.IsFlatInDimensionsGEAfterBaseChange T)) :
    D.flatDimensionFunctor.map (Quiver.Hom.op g) h =
      ⟨D.isFlatInDimensionsGEAfterBaseChange_of_hom g h.down⟩ := rfl

/-- Every value of `F_n` has at most one element, so `F_n` is subterminal. -/
public instance flatDimensionFunctor_obj_subsingleton (D : FlatDimensionSituation.{u})
    (T : (Over D.S)ᵒᵖ) : Subsingleton (D.flatDimensionFunctor.obj T) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => by congr⟩

/-- A value of `F_n` is nonempty exactly when the corresponding base change of the module is
flat over the base in dimensions `≥ n`. -/
@[simp] public theorem flatDimensionFunctor_obj_nonempty_iff
    (D : FlatDimensionSituation.{u}) (T : Over D.S) :
    Nonempty (D.flatDimensionFunctor.obj (Opposite.op T)) ↔
      D.IsFlatInDimensionsGEAfterBaseChange T :=
  ⟨fun ⟨⟨h⟩⟩ => h, fun h => ⟨⟨h⟩⟩⟩

end FlatDimensionSituation

end AlgebraicGeometry
