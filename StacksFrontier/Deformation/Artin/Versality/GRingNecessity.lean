module

public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Hypotheses
public import StacksFrontier.RingTheory.ApproximationProperty.GRing
public import StacksFrontier.RingTheory.ApproximationProperty.Henselization
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes

/-!
# The G-ring hypothesis of Lemma 98.12.7 is necessary (Stacks Example 98.12.8)

Stacks Project, Chapter 98 "Artin's Axioms", Example 98.12.8 (Tag 07XI). Let `Λ` be a Noetherian
ring, `𝔪` a maximal ideal of `Λ` and `R = Λ_𝔪^∧`. For a factorization `Λ → C → R` with `C` of
finite type over `Λ`, put `S = Spec Λ`, `U = S ∖ {𝔪}`, `S' = U ⨿ Spec C`, let `F` be the presheaf
on `(Sch/S)_{fppf}` with `F(T) = *` if `T → S` factors through `S'` and `F(T) = ∅` otherwise,
and let `𝒳 = 𝒮_F` be the associated category fibred in sets. Then `𝒳` is limit preserving on
objects and has an effective versal formal object `ξ` over `R`; if the conclusion of
Lemma 98.12.7 (Tag 07XH) holds for every such `𝒳` (without its hypothesis that `𝒪_{S,s}` is a
G-ring), then `Λ_𝔪` is a G-ring.

## Main results

* `…GRingNecessity.isLimitPreservingOnObjects_and_formalObject_isEffective_isVersal` (in
  `…GRingNecessity.Hypotheses`): the category `𝒳` is limit preserving on objects and `ξ` is an
  effective versal formal object over `R`.
* `…GRingNecessity.exists_lift_smallExtension_of_algebraizationConclusion` (in
  `…GRingNecessity.Datum`): if the conclusion of Lemma 98.12.7 holds for `𝒳` and `ξ`, there are a
  finite type `Λ`-algebra `A` and a maximal ideal `𝔪_A` over `𝔪` with `κ(𝔪) = κ(𝔪_A)`, condition
  (4) of Tag 02HT for `Λ → A` at `𝔪_A`, and a `Λ`-algebra map `C → A`.
* `Deformation.Artin.GRingNecessity.hasApproximationProperty_and_isGRing_henselization`: if the
  conclusion of Lemma 98.12.7 holds for every `𝒳` and `ξ` as above, every henselization of `Λ_𝔪`
  has the approximation property and is a G-ring.
* `Deformation.Artin.GRingNecessity.isGRing_of_forall_algebraizationConclusion`: **Stacks 07XI**,
  under the same hypothesis `Λ_𝔪` is a G-ring.
* `Deformation.Artin.GRingNecessity.isGRing_of_forall_algebraizationLemmaHolds`: the same with
  Lemma 98.12.7 assumed in lemma form, for all formal objects satisfying its hypotheses.

## Implementation notes

The conclusion of Lemma 98.12.7 is `Deformation.Artin.AlgebraizationConclusion`, copied verbatim
from the conclusion of the formalized statement of Tag 07XH
(`Deformation.Artin.exists_finiteType_versal_approximation`), applied to
`𝒳 = factorizationCategory 𝔪 C B hS` and its formal object `ξ = formalObject 𝔪 C φ B hS` over
`R`, for every finite type `Λ`-algebra `C` and every `Λ`-algebra map `φ : C → R`. The site
`(Sch/S)_{fppf}` is a big fppf site `B` containing `S`, as in that formalization of Tag 07XH.

The proof follows the source. From the conclusion of 07XH one reads off the datum of the Example
(`exists_lift_smallExtension_of_algebraizationConclusion`, and with smoothness at `𝔪_A` by Tag
02HT, `algebraizesFiniteTypeFactorizations_of_forall`); a system of polynomial equations over `Λ`
with a solution in `R` then has a solution in the henselization `Λ_𝔪^h`
(`exists_solution_henselization_of_algebraizesFiniteTypeFactorizations`), so `Λ_𝔪^h` has the
approximation property
(`Stacks.ApproximationProperty.hasApproximationProperty_of_forall_exists_solution`).
The source then cites a missing reference ("insert future reference here") for the implication
from the approximation property to the G-ring property: this is Rotthaus' theorem (C. Rotthaus,
*Rings with approximation property*, Math. Ann. 287 (1990), 455–466), formalized here as
`IsLocalRing.HasApproximationProperty.isGRing`. Finally a local ring whose henselization is a
G-ring is a G-ring (`Stacks.ApproximationProperty.isGRing_atPrime_of_isGRing_isHenselization`).

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 04SU](https://stacks.math.columbia.edu/tag/04SU)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466][Rotthaus]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Deformation.Artin.GRingNecessity

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (B : BigFppfSite.{u}) (hS : B.Contains (AlgebraicGeometry.Spec (.of Λ)))

/-- **Stacks Example 98.12.8 (Tag 07XI), the approximation property of `Λ_𝔪^h`.** If the
conclusion of Lemma 98.12.7 holds for the categories `𝒳 = 𝒮_F` and formal objects `ξ` of the
Example, then every henselization `H` of `Λ_𝔪` has the approximation property (a system of
polynomial equations over `H` with a solution in the completion of `H` has a solution in `H`) and
is a G-ring. The second assertion is Rotthaus' theorem, the reference missing in the source. -/
@[stacks 07XI "the approximation property of the henselization `Λ_𝔪^h` and, by Rotthaus' \
theorem (the reference the source leaves missing), that `Λ_𝔪^h` is a G-ring"]
theorem hasApproximationProperty_and_isGRing_henselization
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C], Algebra.FiniteType Λ C →
      ∀ φ : C →ₐ[Λ] Completion 𝔪,
        AlgebraizationConclusion B (AlgebraicGeometry.Spec (.of Λ)) hS
          (factorizationCategory 𝔪 C B hS) (formalObject 𝔪 C φ B hS))
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra Λ H] [Algebra (Localization.AtPrime 𝔪) H]
    [IsScalarTower Λ (Localization.AtPrime 𝔪) H]
    [IsHenselization (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) H] :
    HasApproximationProperty H ∧ IsGRing H := by
  have hdatum := algebraizesFiniteTypeFactorizations_of_forall 𝔪 B hS h
  have hAP : HasApproximationProperty H :=
    Stacks.ApproximationProperty.hasApproximationProperty_of_forall_exists_solution Λ 𝔪 H
      fun _ _ f a ha =>
        exists_solution_henselization_of_algebraizesFiniteTypeFactorizations Λ 𝔪 hdatum H f a ha
  have : IsNoetherianRing H := IsLocalRing.isNoetherianRing_of_isHenselization
    (A := Localization.AtPrime 𝔪) (B := H) (ResidueField (Localization.AtPrime 𝔪))
  exact ⟨hAP, hAP.isGRing⟩

/-- **Stacks Example 98.12.8 (Tag 07XI).** Let `Λ` be a Noetherian ring and `𝔪` a maximal ideal
of `Λ`. If for every finite type `Λ`-algebra `C` and every `Λ`-algebra map `φ : C → Λ_𝔪^∧` the
conclusion of Lemma 98.12.7 (Tag 07XH) holds for the category `𝒳 = 𝒮_F` fibred in sets over the
big fppf site of `S = Spec Λ` attached to `S' = (S ∖ {𝔪}) ⨿ Spec C` and its effective versal formal
object `ξ` over `Λ_𝔪^∧`, then `Λ_𝔪` is a G-ring. -/
@[stacks 07XI "the conclusion of the Example: if the conclusion of Lemma 98.12.7 (07XH) holds \
for every `𝒳 = 𝒮_F` as above, then `Λ_𝔪` is a G-ring; the conclusion of 07XH is \
`AlgebraizationConclusion`, copied verbatim from the formalization of 07XH"]
theorem isGRing_of_forall_algebraizationConclusion
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C], Algebra.FiniteType Λ C →
      ∀ φ : C →ₐ[Λ] Completion 𝔪,
        AlgebraizationConclusion B (AlgebraicGeometry.Spec (.of Λ)) hS
          (factorizationCategory 𝔪 C B hS) (formalObject 𝔪 C φ B hS)) :
    IsGRing (Localization.AtPrime 𝔪) := by
  obtain ⟨H, _, _, _, _, _, hH⟩ := exists_henselization_over_maximalIdeal Λ 𝔪
  have := hH
  exact Stacks.ApproximationProperty.isGRing_atPrime_of_isGRing_isHenselization Λ 𝔪 H
    (hasApproximationProperty_and_isGRing_henselization 𝔪 B hS h H).2

/-- **Stacks Example 98.12.8 (Tag 07XI), with Lemma 98.12.7 assumed in lemma form.** If for
every finite type `Λ`-algebra `C` the statement of Lemma 98.12.7 (Tag 07XH) without its G-ring
hypothesis holds for the category `𝒳 = 𝒮_F` of the Example (`AlgebraizationLemmaHolds`), then
`Λ_𝔪` is a G-ring. -/
@[stacks 07XI "with Lemma 98.12.7 assumed in lemma form (for every formal object of `𝒳` \
satisfying its hypotheses other than the G-ring hypothesis): `Λ_𝔪` is a G-ring"]
theorem isGRing_of_forall_algebraizationLemmaHolds
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C], Algebra.FiniteType Λ C →
      AlgebraizationLemmaHolds 𝔪 B hS C) :
    IsGRing (Localization.AtPrime 𝔪) :=
  isGRing_of_forall_algebraizationConclusion 𝔪 B hS fun C _ _ hC φ =>
    algebraizationConclusion_of_algebraizationLemmaHolds 𝔪 B hS C (h C hC) φ

end Deformation.Artin.GRingNecessity

end
