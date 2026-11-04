module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafReindex

/-!
# Stacks 09RI for the system of base changes of Situation 0DKU

Situation 0DKU, `AlgebraicGeometry.Space.RelativeDescentSituation`, carries a directed inverse
system `Y_i` of quasi-compact quasi-separated algebraic spaces with affine transitions, its
limit, a flat finitely presented `p₀ : X₀ ⟶ Y_0`, and the base changes `X_i = X₀ ×_{Y_0} Y_i` and
`X = X₀ ×_{Y_0} Y` with their projections.  Those base changes, their projections `X_i ⟶ X₀`,
their transition morphisms and the projections `X ⟶ X_i` form a
`CategoryTheory.PullbackData.LimitSystem` over `X₀` indexed by the later stages,
`AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem`.  This file proves the
conclusion of Stacks 09RI for that system,
`AlgebraicGeometry.Space.RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent`.

The statement for Situation 09RH,
`AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent`, is the case
`X₀ = Y_0`, `p₀ = 𝟙` of this one, by
`AlgebraicGeometry.Space.DescentSituation.sourceLimitSystem_relativeSituation`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem`: the system of base
  changes of Situation 0DKU, as a `CategoryTheory.PullbackData.LimitSystem` over `X₀`.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.projHom_sourceLimitSystem_eq_homComparison`
  and `trans_sourceLimitSystem_eq_homTransition`: the maps to the vertex and the transition maps
  of that system are those of the system of homomorphism groups of Stacks 0DKV.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent`:
  **Stacks 09RI's conclusion for the system of base changes of Situation 0DKU.**
* `AlgebraicGeometry.Space.DescentSituation.sourceLimitSystem_relativeSituation`: the system of
  stages of Situation 09RH is the case `p₀ = 𝟙`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Situation 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-! ### The system of base changes of Situation 0DKU -/

/-- **The base changes of Situation 0DKU as a system over `X₀` with a cone.**  Its stages are the
base changes `X_i = X₀ ×_{Y_0} Y_i` at the later stages, its structure morphisms the projections
`X_i ⟶ X₀`, its transition morphisms the `f_{ji}`, and its vertex the base change
`X = X₀ ×_{Y_0} Y` at the limit with the projections `f_i : X ⟶ X_i`. -/
def sourceLimitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) D.initialSource D.LaterIndex where
  stage := D.stageSource
  toBase := D.stageToInitial
  transition h := D.sourceTransition h
  transition_toBase h := D.sourceTransition_comp_stageToInitial h
  transition_comp h h' := D.sourceTransition_comp_sourceTransition h h'
  limit := D.limitSource
  limitToBase := D.limitToInitial
  proj := D.sourceProjection
  proj_toBase := D.sourceProjection_comp_stageToInitial
  proj_transition h := D.sourceProjection_comp_sourceTransition h

/-! ### The two systems of homomorphism groups coincide -/

variable (K₀ L₀ : derivedModules B S hS D.initialSource)

/-- **The maps to the vertex of the system of base changes are the comparison maps of Stacks
0DKV.**  Both are the derived pullback along the projection `f_i : X ⟶ X_i`, conjugated by the
identification of the factorisation `f_i ≫ f_{i0} = f_0` of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`. -/
theorem projHom_sourceLimitSystem_eq_homComparison (i : D.LaterIndex) :
    D.sourceLimitSystem.projHom (canonicalPullbackData B S hS) K₀ L₀ i =
      D.homComparison (DerivedPullbackComposition.canonical B S hS) K₀ L₀ i := by
  funext φ
  rw [projHom_canonicalPullbackData]
  exact (DerivedPullbackComposition.factorHom_eq_comp _ _ _ _ _ _ _ φ).symm

/-- **The transition maps of the system of base changes are the transition maps of Stacks
0DKV.** -/
theorem trans_sourceLimitSystem_eq_homTransition {i j : D.LaterIndex} (h : i ≤ j) :
    D.sourceLimitSystem.trans (canonicalPullbackData B S hS) K₀ L₀ i j h =
      D.homTransition (DerivedPullbackComposition.canonical B S hS) K₀ L₀
        (show i.1 ≤ j.1 from h) := by
  funext φ
  rw [trans_canonicalPullbackData]
  exact (DerivedPullbackComposition.factorHom_eq_comp _ _ _ _ _ _ _ φ).symm

/-- The maps to the vertex of the system of base changes, for the pullback-pseudofunctor datum of
the total left derived functor, are the comparison maps of Stacks 0DKV. -/
theorem projHom_smallEtale_sourceLimitSystem_eq_homComparison (i : D.LaterIndex) :
    D.sourceLimitSystem.projHom (smallEtaleDerivedPullbackData B S hS) K₀ L₀ i =
      D.homComparison (DerivedPullbackComposition.canonical B S hS) K₀ L₀ i := by
  rw [← projHom_canonicalPullbackData_eq_smallEtale D.sourceLimitSystem K₀ L₀]
  exact projHom_sourceLimitSystem_eq_homComparison D K₀ L₀ i

/-- The transition maps of the system of base changes, for the pullback-pseudofunctor datum of
the total left derived functor, are the transition maps of Stacks 0DKV. -/
theorem trans_smallEtale_sourceLimitSystem_eq_homTransition {i j : D.LaterIndex} (h : i ≤ j) :
    D.sourceLimitSystem.trans (smallEtaleDerivedPullbackData B S hS) K₀ L₀ i j h =
      D.homTransition (DerivedPullbackComposition.canonical B S hS) K₀ L₀
        (show i.1 ≤ j.1 from h) := by
  rw [← trans_canonicalPullbackData_eq_smallEtale D.sourceLimitSystem K₀ L₀]
  exact trans_sourceLimitSystem_eq_homTransition D K₀ L₀ h

/-! ### Stacks 09RI for the system of base changes of Situation 0DKU -/

/-- **Stacks 09RI's conclusion for the system of base changes of Situation 0DKU.**  In Situation
0DKU, indexed by a directed preorder `I` in the universe of the site with fewer elements than the
cofinality of the site's size cutoff, let `K₀` and `L₀` be objects of `D(𝒪_{X₀})` with `K₀`
pseudo-coherent and `L₀` in `D_QCoh(𝒪_{X₀})` of locally finite Tor dimension along `p₀`.  Then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*K₀, Lf_0^*L₀)`

is bijective, for the system
`AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem` of base changes.

The statement for Situation 09RH,
`AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent`, is the case
`X₀ = Y_0`, `p₀ = 𝟙` of this one. -/
theorem isColim_sourceLimitSystem_of_pseudoCoherent (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hK : IsPseudoCoherentObject K₀) (hL : IsInQuasicoherentDerived D.initialSource L₀)
    (hTor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    D.sourceLimitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) K₀ L₀ := by
  obtain ⟨hsurj, hinj⟩ :=
    homDescentOfPseudoCoherent_proved I D (D.isSchemeLimit_of_size hI) K₀ L₀ hK hL hTor
  refine ⟨fun i j h s =>
    PullbackData.LimitSystem.projHom_trans
      (smallEtaleDerivedPullbackData_isCoherent B S hS) K₀ L₀ h s, fun t => ?_,
    fun i s s' hss => ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hsurj t
    refine ⟨i, φ, ?_⟩
    rwa [projHom_smallEtale_sourceLimitSystem_eq_homComparison]
  · rw [projHom_smallEtale_sourceLimitSystem_eq_homComparison] at hss
    obtain ⟨j, h, hj⟩ := hinj i s s' hss
    refine ⟨j, h, ?_⟩
    rwa [trans_smallEtale_sourceLimitSystem_eq_homTransition]

/-- **Stacks 09RI's conclusion for the system of base changes of Situation 0DKU, for the
canonical pullback-pseudofunctor datum.**  The two data give the same statement,
`AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff`. -/
theorem isColim_canonicalPullbackData_sourceLimitSystem_of_pseudoCoherent
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hK : IsPseudoCoherentObject K₀) (hL : IsInQuasicoherentDerived D.initialSource L₀)
    (hTor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    D.sourceLimitSystem.IsColim (canonicalPullbackData B S hS) K₀ L₀ :=
  (isColim_canonicalPullbackData_iff D.sourceLimitSystem K₀ L₀).2
    (isColim_sourceLimitSystem_of_pseudoCoherent D K₀ L₀ hI hK hL hTor)

end RelativeDescentSituation

/-! ### The statement for Situation 09RH is the case `p₀ = 𝟙` -/

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The system of stages of Situation 09RH over its chosen stage is the system of base changes
of its reading as Situation 0DKU with `p₀ = 𝟙`.**  Both have the stages `X_i` for `i ≥ 0` with
the morphisms `f_{i0}`, the transition morphisms `f_{ji}`, and the limit `X` with its
projections; under
`AlgebraicGeometry.Space.DescentSituation.relativeSituation` these are the same data. -/
theorem sourceLimitSystem_relativeSituation :
    D.relativeSituation.sourceLimitSystem = D.limitSystem :=
  rfl

-- `AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent` is the case
-- `relativeSituation` of `RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent`.
example (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hI : Cardinal.mk I < B.cutoff.ord.cof) (hE : IsPseudoCoherentObject E₀)
    (hK : IsInQuasicoherentDerived (D.stage D.base) K₀)
    (hTor : HasLocallyFiniteTorDimensionAlong (𝟙 (D.stage D.base)) K₀) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent D.relativeSituation E₀ K₀
    hI hE hK hTor

end DescentSituation

end AlgebraicGeometry.Space

end
