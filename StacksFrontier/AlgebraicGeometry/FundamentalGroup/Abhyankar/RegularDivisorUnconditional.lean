module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.RegularDivisor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.EtaleLocallyStandard
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# Abhyankar's lemma for a regular divisor

Let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor which is a regular
scheme and `f : Y ⟶ X ∖ D` finite étale and tamely ramified over `X` in codimension one. Then
étale locally on `X` the morphism `Y ⟶ X` is a finite disjoint union of standard tamely ramified
morphisms ([Stacks, Example 0EYF]). This is [Stacks, Tag 0EYG].

## Main results

* `AlgebraicGeometry.isEtaleLocallyStandardTamelyRamified_of_isTamelyRamifiedInCodimensionOne`:
  [Stacks, Tag 0EYG].
* `Stacks.FundamentalGroup.IsEtaleLocallyStandardTamelyRamified.of_isRegularRing`: the étale
  local form with `A / φA` regular implies the property, in which `A / φA` is only reduced.

## Implementation notes

The proof of the source is
`AlgebraicGeometry.exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne`, which
takes two arguments: purity for regular local rings ([Stacks, Tag 0BMA] (1)), discharged by
`AlgebraicGeometry.purityAtRegularLocalRings`, and the tame half of [Stacks, Tag 0EYD],
discharged by `Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne`. Its
conclusion has `A / φA` regular, which is stronger than the requirement of [Stacks, Example 0EYF]
that `A / φA` be reduced: a regular ring is reduced, as its localizations at maximal ideals are
regular local rings, hence domains.

"`D` is a regular scheme" is `AlgebraicGeometry.IsRegular D.subscheme` ([Stacks, Tag 02IS]), and
"`Y` is tamely ramified over `X` in codimension one" is
`Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne` for the inclusion of `X ∖ D`.

## References

* [Stacks Project, Lemma 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Example 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- The étale local form produced by Abhyankar's lemma, with `A / φA` regular, implies
`IsEtaleLocallyStandardTamelyRamified`, where `A / φA` is only required to be reduced: a regular
ring is reduced. -/
theorem IsEtaleLocallyStandardTamelyRamified.of_isRegularRing {X Y : Scheme.{u}} {U : X.Opens}
    {f : Y ⟶ U}
    (h : ∀ x : X, ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A),
      g a = x ∧ ∃ φ : A, IsNoetherianRing A ∧ φ ∈ nonZeroDivisors A ∧
        IsRegularRing (A ⧸ Ideal.span {φ}) ∧
        ∃ gU : Spec (.of (Localization.Away φ)) ⟶ U,
          IsPullback gU (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))))
            U.ι g ∧
          ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : A)) ∧
            ∃ ι : pullback f gU ≅ ∐ fun i ↦ Spec (.of (Localization.Away
                (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ))),
              ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedCover A φ (e i)) =
                pullback.snd f gU) :
    IsEtaleLocallyStandardTamelyRamified U f := by
  intro x
  obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, rest⟩ := h x
  refine ⟨A, g, hg, a, hga, φ, hA, hφ, ?_, rest⟩
  exact isReduced_ofLocalizationMaximal _ fun p hp ↦ by
    have : p.IsPrime := hp.isPrime
    have : IsDomain (Localization.AtPrime p) := IsRegularLocalRing.isDomain _
    infer_instance

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

open Stacks.FundamentalGroup

/-- **Abhyankar's lemma for a regular divisor, [Stacks, Tag 0EYG].** Let `X` be a locally
Noetherian scheme and let `D ⊆ X` be an effective Cartier divisor such that `D` is a regular
scheme. Let `f : Y ⟶ X ∖ D` be a finite étale morphism. If `Y` is tamely ramified over `X` in
codimension one, then étale locally on `X` the morphism `Y ⟶ X` is a finite disjoint union of
standard tamely ramified morphisms as described in [Stacks, Example 0EYF]: every `x ∈ X` lies in
the image of an étale `Spec A ⟶ X` with `A` Noetherian, on which `X ∖ D` is `Spec A_φ` for a
nonzerodivisor `φ` with `A / φA` reduced, and over which `Y` is
`∐ᵢ Spec (A[x]/(x^{eᵢ} - φ))_φ` with each `eᵢ ≥ 1` invertible in `A`.

Here `D` is the closed subscheme `D.subscheme` cut out by the ideal sheaf `D`, and `X ∖ D` is the
open subscheme `D.support.compl`. -/
@[stacks 0EYG "Abhyankar's lemma for a regular divisor: a finite étale cover of `X ∖ D` tamely \
ramified in codimension one is étale locally on `X` a finite disjoint union of the standard \
tamely ramified covers of Example 0EYF"]
theorem isEtaleLocallyStandardTamelyRamified_of_isTamelyRamifiedInCodimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hDreg : IsRegular D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (Scheme.Opens.ι (D.support.compl : X.Opens)) f) :
    IsEtaleLocallyStandardTamelyRamified (D.support.compl : X.Opens) f := by
  have h := (isRegular_tfae D.subscheme).out 1 2
  have hstalk := (h.mp hDreg).2
  refine IsEtaleLocallyStandardTamelyRamified.of_isRegularRing fun x ↦ ?_
  obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, gU, -, hpb, n, e, he, ι, hι⟩ :=
    exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne
      purityAtRegularLocalRings
      (fun S hS ↦ pulledBackCover_isTamelyRamifiedInCodimensionOne S hS) D hD hstalk f htame x
  exact ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, gU, hpb, n, e, he, ι, hι⟩

end AlgebraicGeometry

end
