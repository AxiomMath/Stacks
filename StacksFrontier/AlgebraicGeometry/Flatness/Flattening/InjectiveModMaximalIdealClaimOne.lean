module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.InjectiveModMaximalIdealClaims
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.QuotientSituation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFibreInjectivityAllPrimes

/-!
# Stacks 05U9 from Claim 1 of its proof

The proof of Stacks 05U9 reduces, through Stacks 0AT2, to the case where the local algebra `B` is
the localization at a prime of a polynomial algebra over `A` and the module `N` is of finite
presentation over `B`, and then establishes two claims about that case:

* **Claim 1**: some finitely generated nilpotent ideal `I ⊆ A` has `N/IN` flat over `A/I`; and
* **Claim 2**: for every prime `𝔭 ⊆ A` the map `u ⊗ id_{κ(𝔭)}` is injective.

`AlgebraicGeometry.conclusion_of_claims` derives the three conclusions of Stacks 05U9 from the
two claims. This file removes Claim 2 from that input, and with it the prime-by-prime flatness
that Claim 2 consumes: `AlgebraicGeometry.rTensor_residueField_injective_of_claims` proves Claim
2 from flatness of `N/𝔮N` over `A/𝔮` at every prime `𝔮`, and
`AlgebraicGeometry.flat_quotient_primes_of_isNilpotent` supplies that from the nilpotent ideal of
Claim 1, because a nilpotent ideal lies in every prime. So the three conclusions of Stacks 05U9
rest on the nilpotent-ideal statement alone.

## Main results

* `AlgebraicGeometry.conclusion_of_claim1`: the three conclusions of Stacks 05U9 in Situation
  0AT0, from Claim 1 alone.
* `AlgebraicGeometry.universallyInjective_of_claim1`,
  `AlgebraicGeometry.finitePresentation_of_claim1`, `AlgebraicGeometry.flat_of_claim1`: the three
  conclusions separately.
* `AlgebraicGeometry.conclusion_of_claim1_of_presentation`: the three conclusions for a *single*
  localized-polynomial situation from Claim 1 for that situation, rather than from Claim 1 for
  every situation over the same base local ring. This is the shape an induction on the length of
  a generic flatness stratification can feed, since its induction hypothesis is the proposition
  over the specific quotients `A ⧸ K_i` and `A ⧸ Jⁿ`.
* `AlgebraicGeometry.conclusion_quotient_of_claim1_of_presentation`: the same over a quotient
  `A ⧸ E` of the base, which is where the induction applies it.

## Implementation notes

Nothing here proves Stacks 05U9 and nothing here carries its tag: Claim 1 is a hypothesis. What
remains of it in this repository is the generic flatness stratification of Stacks 0ASY
(`AlgebraicGeometry.exists_flat_stratification`) read as a chain of finitely generated ideals of
`A`, which is what feeds `Stacks.flat_of_least_flattening_of_flat_away` and
`Stacks.exists_fg_isNilpotent_flat_quotient_of_least`; those two are proved, and so is the
smallest flattening ideal of Stacks 05PG that they consume, in the shape
`Module.FlatAtPointSituation.exists_ideal_flat_quotient_iff_le_of_henselian`.

By `Stacks.not_forall_exists_fg_isNilpotent_flat_quotient` the nilpotent-ideal statement is false
for `N` alone, so Claim 1 is genuinely a statement about the data of Situation 0AT0.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT2](https://stacks.math.columbia.edu/tag/0AT2)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- Claim 1 gives injectivity of `u` on every residue field. -/
private theorem rTensor_residueField_injective_of_claim1
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B) [Module.FinitePresentation S.B S.N]
    (hclaim1 : ∃ I : Ideal S.A, IsNilpotent I ∧
      Module.Flat (S.A ⧸ I) (S.N ⧸ (I • (⊤ : Submodule S.A S.N))))
    (q : Ideal S.A) [q.IsPrime] : Function.Injective (S.u.rTensor q.ResidueField) := by
  obtain ⟨I, hnil, hflat⟩ := hclaim1
  exact rTensor_residueField_injective_of_claims S P
    (fun r _ => flat_quotient_primes_of_isNilpotent hnil hflat r) q

/-- **Stacks 05U9 from Claim 1 of its proof.** In Situation 0AT0, suppose that in every special
case singled out by Stacks 0AT2 — the local algebra a localization of a polynomial algebra over
`A` at a prime, the module finitely presented over it — Claim 1 of the source's proof holds: some
nilpotent ideal `I ⊆ A` has `N ⧸ IN` flat over `A ⧸ I`.

Then all three conclusions of Stacks 05U9 hold: `u` is `A`-universally injective, `N` is of finite
presentation over `B`, and `N` is flat over `A`.

Claim 2 of the source's proof is supplied by
`AlgebraicGeometry.rTensor_residueField_injective_of_claims`, whose prime-by-prime flatness comes
from the nilpotent ideal by `AlgebraicGeometry.flat_quotient_primes_of_isNilpotent`. So this
strengthens `AlgebraicGeometry.conclusion_of_claims`, whose input also contains Claim 2. -/
theorem conclusion_of_claim1
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hclaim1 : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        ∃ I : Ideal T.A, IsNilpotent I ∧
          Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) :
    UniversallyInjectivePoly.{_, u₅} S.u ∧
      Module.FinitePresentation S.B S.N ∧ Module.Flat S.A S.N := by
  refine conclusion_of_claims S fun T hbase P hfp => ?_
  let := hfp
  exact ⟨hclaim1 T hbase P hfp, fun q _ => rTensor_residueField_injective_of_claim1 T P
    (hclaim1 T hbase P hfp) q⟩

/-- **The universal-injectivity conclusion of Stacks 05U9 from Claim 1 of its proof.** -/
theorem universallyInjective_of_claim1
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hclaim1 : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        ∃ I : Ideal T.A, IsNilpotent I ∧
          Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) :
    UniversallyInjectivePoly.{_, u₅} S.u :=
  (conclusion_of_claim1.{u₁, u₂, u₃, u₄, u₅} S hclaim1).1

/-- **The finite-presentation conclusion of Stacks 05U9 from Claim 1 of its proof.** -/
theorem finitePresentation_of_claim1
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hclaim1 : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        ∃ I : Ideal T.A, IsNilpotent I ∧
          Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) :
    Module.FinitePresentation S.B S.N :=
  (conclusion_of_claim1.{u₁, u₂, u₃, u₄, u₁} S hclaim1).2.1

/-- **The flatness conclusion of Stacks 05U9 from Claim 1 of its proof.** -/
theorem flat_of_claim1
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hclaim1 : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        ∃ I : Ideal T.A, IsNilpotent I ∧
          Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) :
    Module.Flat S.A S.N :=
  (conclusion_of_claim1.{u₁, u₂, u₃, u₄, u₁} S hclaim1).2.2


/-- **Stacks 05U9 from Claim 1 of its proof, in a single localized-polynomial case.** In
Situation 0AT0, suppose the local algebra `B` is presented as the localization at a prime of a
polynomial algebra over `A` in finitely many variables, that `N` is of finite presentation over
`B`, and that Claim 1 of the source's proof holds *for this situation*: some nilpotent ideal
`I ⊆ A` has `N ⧸ IN` flat over `A ⧸ I`. Then all three conclusions of Stacks 05U9 hold for it.

This differs from `AlgebraicGeometry.conclusion_of_claim1` in taking Claim 1 for the one
situation at hand rather than for every situation over the same base local ring. That is what an
induction on the length of a generic flatness stratification can supply: the induction
hypothesis is the proposition over `A ⧸ K_i` and over `A ⧸ Jⁿ`, which are specific situations,
not all situations over a fixed base.

Claim 2 of the source's proof is supplied, as in
`AlgebraicGeometry.conclusion_of_claim1`, by
`AlgebraicGeometry.rTensor_residueField_injective_of_claims` together with
`AlgebraicGeometry.flat_quotient_primes_of_isNilpotent`. -/
theorem conclusion_of_claim1_of_presentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N)
    (hclaim1 : ∃ I : Ideal S.A, IsNilpotent I ∧
      Module.Flat (S.A ⧸ I) (S.N ⧸ (I • (⊤ : Submodule S.A S.N)))) :
    InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} S := by
  let := P.prime_isPrime
  let := P.polynomialAlgebra
  let := P.scalarTower
  let := P.isLocalization
  let := hfp
  obtain ⟨I, hnil, hflat⟩ := hclaim1
  let := hflat
  have hu : UniversallyInjectivePoly.{_, max u₁ u₅} S.u :=
    universallyInjective_of_isNilpotent_of_flat_quotient_of_fibres
      (B := S.B) P.prime.primeCompl S.u I hnil
      (fun q _ => rTensor_residueField_injective_of_claim1 S P ⟨I, hnil, hflat⟩ q)
  exact ⟨hu, hfp, flat_of_universallyInjective_into_flat S.u hu⟩

/-- **The induction step in the proof of Claim 1 of Stacks 05U9.** In Situation 0AT0, with `B`
presented as the localization at a prime of a polynomial algebra over `A` and `N` of finite
presentation over `B`, let `E ⊆ A` be a proper ideal. Suppose Claim 1 of the source's proof
holds for the reduction of the situation modulo `E`: some nilpotent ideal of `A ⧸ E` makes the
reduction of `N` flat. Then the three conclusions of Stacks 05U9 hold for that reduction.

The reduced data are Situation 0AT0 again
(`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotient`), the presentation reduces
with the same number of variables
(`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientPresentation`) and finite
presentation of the reduced module is base change
(`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.finitePresentation_quotient_N`), so
`AlgebraicGeometry.conclusion_of_claim1_of_presentation` applies over `A ⧸ E`.

This is the shape the induction on the length of a generic flatness stratification needs: the
stratification of `N ⧸ EN` over `A ⧸ E` produced by
`Stacks.FlatStratification.quotient` is shorter, and the proposition it has to supply over
`A ⧸ E` is this one. -/
theorem conclusion_quotient_of_claim1_of_presentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N)
    (E : Ideal S.A) (hE : E ≤ IsLocalRing.maximalIdeal S.A)
    (hclaim1 : ∃ I : Ideal (S.quotient E hE).A, IsNilpotent I ∧
      Module.Flat ((S.quotient E hE).A ⧸ I)
        ((S.quotient E hE).N ⧸ (I • (⊤ : Submodule (S.quotient E hE).A (S.quotient E hE).N)))) :
    InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} (S.quotient E hE) := by
  let := hfp
  exact conclusion_of_claim1_of_presentation (S.quotient E hE) (S.quotientPresentation E hE P)
    (S.finitePresentation_quotient_N E hE) hclaim1

end AlgebraicGeometry

end
