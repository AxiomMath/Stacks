module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseUnboundedDerivedIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeAffineChartwise
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFactorizationEnoughObjects

/-!
# Isomorphisms in `D(𝒪_T)` are étale local on the base of a morphism `T ⟶ Y'`

Let `p : T ⟶ Y'` be a morphism of algebraic spaces. A morphism of `𝒪_T`-modules, or of the
unbounded derived category `D(𝒪_T)`, is invertible as soon as its restriction to `T ×_{Y'} W` is
invertible for every étale scheme chart `W` of `Y'` with affine underlying scheme. This is the
reduction "this we may check étale locally on `Y'`, hence we may assume `Y'` affine" in the proof
of Stacks Tag 0DL7, applied with `p` the two maps `Y ⟶ Y'` and `X' ⟶ Y'` into the pushout.

The geometric input is on base: the affine charts of `T` whose composite to `Y'` factors through
an affine chart of `Y'` are enough objects of the small étale site of `T`
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChartFactorsThroughAffineChart`), and such a
family detects isomorphisms of modules (`AlgebraicGeometry.Space.
isIso_of_forall_isIso_etaleModulePullback_chartToSpace_of_hasEnoughObjects`).
A chart `V` of `T` with `V ⟶ T ⟶ Y'` factoring through the chart `W` of `Y'` factors through the
projection `T ×_{Y'} W ⟶ T`, and restriction of modules is compatible with composition
(`AlgebraicGeometry.Space.modulePullbackCompIso`, Stacks 03LU). The derived statement follows
through the cohomology sheaves, as in
`AlgebraicGeometry.Space.isIso_iff_forall_isIso_flatModuleDerivedPullback_chartToSpace`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_forall_isIso_modulePullback_pullbackFst`: the statement for
  morphisms of `𝒪_T`-modules.
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_flatModuleDerivedPullback_pullbackFst`: the
  statement in `D(𝒪_T)`, at any models of the derived categories.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {T Y' : AlgebraicSpaces B S hS} (p : T ⟶ Y')

/-- The projection `T ×_{Y'} W ⟶ T` of the base change of an étale chart `W` of `Y'` is étale. -/
theorem isEtale_pullbackFst_chartToSpace (W : SmallEtale B S hS Y'.obj) :
    IsEtale B S hS (pullback.fst p (chartToSpace B S hS Y' W)).hom :=
  isEtale_of_isPullback B S hS (pullback.snd p (chartToSpace B S hS Y' W))
    (pullback.fst p (chartToSpace B S hS Y' W)) (chartToSpace B S hS Y' W) p
    (IsPullback.of_hasPullback p (chartToSpace B S hS Y' W)).flip
    (isEtale_chartToSpace B S hS Y' W)

/-- The projection `T ×_{Y'} W ⟶ T` is flat, as a morphism of small étale ringed topoi. -/
theorem smallEtaleRingedToposHom_pullbackFst_chartToSpace_isFlat (W : SmallEtale B S hS Y'.obj) :
    (smallEtaleRingedToposHom B S hS (pullback.fst p (chartToSpace B S hS Y' W))).IsFlat :=
  (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS _).1
    (isFlat_of_isEtale B S hS (isEtale_pullbackFst_chartToSpace B S hS p W))

/-- **Isomorphisms of `𝒪_T`-modules are étale local on `Y'`.** For a morphism `p : T ⟶ Y'` of
algebraic spaces, a morphism of `𝒪_T`-modules whose restriction to `T ×_{Y'} W` is invertible for
every étale chart `W` of `Y'` with affine underlying scheme is invertible. -/
theorem isIso_of_forall_isIso_modulePullback_pullbackFst
    {M N : Modules.{u, u} B S hS T.obj T.property} (φ : M ⟶ N)
    (h : ∀ W : SmallEtale B S hS Y'.obj, IsAffineChart B S hS Y'.obj W →
      IsIso ((modulePullback B S hS (pullback.fst p (chartToSpace B S hS Y' W))).map φ)) :
    IsIso φ := by
  refine isIso_of_forall_isIso_etaleModulePullback_chartToSpace_of_hasEnoughObjects B S hS T
    (hasEnoughObjects_isAffineChartFactorsThroughAffineChart B S hS p) φ ?_
  rintro V ⟨-, W, m, hW, hm⟩
  let q : chartSpace B S hS T V ⟶ pullback p (chartToSpace B S hS Y' W) :=
    pullback.lift (chartToSpace B S hS T V) (chartSpaceMapOver B S hS m)
      (chartSpaceMapOver_comp_chartToSpace B S hS p m hm).symm
  have hq : q ≫ pullback.fst p (chartToSpace B S hS Y' W) = chartToSpace B S hS T V :=
    pullback.lift_fst _ _ _
  rw [← NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS
    (chartToSpace B S hS T V) (isEtale_chartToSpace B S hS T V)), ← hq,
    ← NatIso.isIso_map_iff (modulePullbackCompIso B S hS q
      (pullback.fst p (chartToSpace B S hS Y' W)))]
  have := h W hW
  exact (inferInstance : IsIso ((modulePullback B S hS q).map
    ((modulePullback B S hS (pullback.fst p (chartToSpace B S hS Y' W))).map φ)))

variable [HasDerivedCategory.{w} (Modules.{u, u} B S hS T.1 T.2)]
  [∀ W : SmallEtale B S hS Y'.obj, HasDerivedCategory.{w'}
    (Modules.{u, u} B S hS (pullback p (chartToSpace B S hS Y' W)).1
      (pullback p (chartToSpace B S hS Y' W)).2)]

/-- **Isomorphisms in `D(𝒪_T)` are étale local on `Y'`.** For a morphism `p : T ⟶ Y'` of algebraic
spaces, a morphism of the unbounded derived category of `𝒪_T`-modules whose restriction to
`T ×_{Y'} W` is invertible for every étale chart `W` of `Y'` with affine underlying scheme is
invertible. -/
theorem isIso_of_forall_isIso_flatModuleDerivedPullback_pullbackFst
    {K L : DerivedCategory (Modules.{u, u} B S hS T.1 T.2)} (φ : K ⟶ L)
    (h : ∀ W : SmallEtale B S hS Y'.obj, IsAffineChart B S hS Y'.obj W →
      IsIso ((flatModuleDerivedPullback B S hS (pullback.fst p (chartToSpace B S hS Y' W))
        (smallEtaleRingedToposHom_pullbackFst_chartToSpace_isFlat B S hS p W)).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  exact isIso_of_forall_isIso_modulePullback_pullbackFst B S hS p _ fun W hW ↦
    (isIso_flatModuleDerivedPullback_map_iff B S hS _ _ φ).1 (h W hW) n

end AlgebraicGeometry.Space

end
