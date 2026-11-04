module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseThree
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.PieceHomExt

/-!
# Stacks Tag 01O9: the triple `(U(ψ), r_{ℒ,ψ}, θ)` is characterized by properties (1), (2), (3)

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : X ⟶ S` a morphism, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras.
[Stacks, Tag 01O9] says that the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` and the map of graded
algebras `θ : r_{ℒ,ψ}^*(⨁_{d ≥ 0} 𝒪(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U(ψ)}` are characterized by its
properties (1), (2) and (3). Following the source, the uniqueness is local over the base: over
each affine open `V` of the base, property (3) identifies the restriction of a triple with the
triple of [Stacks, Tag 01NK] for the induced datum, which is unique, and the restrictions glue.

## Main results

* `…Triple.isTriple_canonical`: `(U(ψ), r_{ℒ,ψ}, θ)` has properties (1), (2) and (3).
* `…Triple.eq_canonical`: **every triple `(U', r', θ')` with properties (1), (2) and (3) is
  `(U(ψ), r_{ℒ,ψ}, θ)`**; property (3) alone forces it.
* `…Triple.existsUnique_isTriple`: the two together.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}

namespace Triple

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **Property (3) forces `θ'`**: a map of graded algebras
`θ' : r_{ℒ,ψ}^*(⨁_{d ≥ 0} 𝒪(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U(ψ)}` such that `(U(ψ), r_{ℒ,ψ}, θ')` has
property (3) is `θ` in degrees `≥ 0`. Over every affine open `V` of the base, both inverse images
along `U(ψ') ⟶ U(ψ)`, read through the same identifications, are [Stacks, Tag 01NK]'s `θ` for the
induced datum; so the two inverse images agree, and the inclusions cover. -/
theorem eq_ofHom_theta_of_isClauseThree (P : GradedPowerMap A f)
    {θ' : GradedNonnegHom
      (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
        (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra)
      (laurentOn P.L P.coveringOpen)}
    (h : IsClauseThree P ⟨P.coveringOpen, P.globalMorphism (relativeProj A), θ'⟩) :
    θ' = GradedNonnegHom.ofHom P.theta := by
  refine GradedNonnegHom.ext fun n => P.hom_ext_of_pullback_affineDatumInclusion fun V => ?_
  obtain ⟨hj, H⟩ := (h V).2 (P.affineDatumInclusion V) (P.affineDatumInclusion_ι V)
  obtain ⟨hj', H'⟩ := (P.isClauseThree_theta V).2 (P.affineDatumInclusion V)
    (P.affineDatumInclusion_ι V)
  have hs : sourceIso P ⟨P.coveringOpen, P.globalMorphism (relativeProj A), θ'⟩ V
      (P.affineDatumInclusion V) hj n =
      sourceIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V
        (P.affineDatumInclusion V) hj' n := rfl
  have ht : targetIso P ⟨P.coveringOpen, P.globalMorphism (relativeProj A), θ'⟩ V
      (P.affineDatumInclusion V) (P.affineDatumInclusion_ι V) n =
      targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V
        (P.affineDatumInclusion V) (P.affineDatumInclusion_ι V) n := rfl
  have e := (H n).trans (H' n).symm
  rw [hs, ht] at e
  exact (Iso.cancel_iso_hom_right _ _ _).1 ((Iso.cancel_iso_inv_left _ _ _).1 e)

/-- **`(U(ψ), r_{ℒ,ψ}, θ)` has properties (1), (2) and (3).** -/
theorem isTriple_canonical (ψ : Twisting f (situationAlgebra A) 1 L) :
    IsTriple ψ (canonical (toGradedPowerMap ψ)) :=
  ⟨isClauseOne_canonical _, isClauseTwo_canonical ψ, (toGradedPowerMap ψ).isClauseThree_theta⟩

/-- **The characterization of [Stacks, Tag 01O9]**: every triple `(U', r', θ')` — an open `U'` of
`X`, a morphism `r' : U' ⟶ Proj_S(𝒜)` and a map of graded algebras
`θ' : r'^*(⨁_{d ≥ 0} 𝒪(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U'}` — with properties (1), (2) and (3) is
`(U(ψ), r_{ℒ,ψ}, θ)`. Property (3) alone forces it. -/
theorem eq_canonical {ψ : Twisting f (situationAlgebra A) 1 L} {t : Triple A L}
    (h : IsTriple ψ t) : t = canonical (toGradedPowerMap ψ) := by
  obtain ⟨θ', rfl⟩ := exists_eq_of_isClauseThree h.2.2
  rw [eq_ofHom_theta_of_isClauseThree _ h.2.2]
  rfl

/-- **The triple `(U(ψ), r_{ℒ,ψ}, θ)` is characterized by properties (1), (2) and (3)**: it has
them, and it is the only triple that does. -/
theorem existsUnique_isTriple (ψ : Twisting f (situationAlgebra A) 1 L) :
    ∃! t : Triple A L, IsTriple ψ t :=
  ⟨canonical (toGradedPowerMap ψ), isTriple_canonical ψ, fun _ h => eq_canonical h⟩

end Triple

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
