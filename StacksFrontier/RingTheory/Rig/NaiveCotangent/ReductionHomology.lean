module

public import StacksFrontier.RingTheory.NaiveCotangent.PresentationHomology
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Annihilation
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReducedPresentation

/-!
# Condition (4) of Stacks 0AJU, read off the presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` be an object of the category
(Stacks 0AL4) and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`.  Writing
`Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, condition (0AJX) of Stacks 0AJU asks that one power of `I`
annihilate `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0` and every `n ≥ 1`.  The source's `NL_{Bₙ/Aₙ}` is
the naive cotangent complex of `Bₙ` over `Aₙ`, which is a *presentation-free* object: it is
computed from the tautological presentation `Aₙ[Bₙ] → Bₙ`, as
`Algebra.naiveCotangentComplex Aₙ Bₙ`, and its two cohomology modules are the categorical
homology of a `HomologicalComplex.double` in degrees `1` and `0`.

This file turns that condition into one about the presentation
`Rig.CompletedPolynomialPresentation.reductionGenerators`, i.e. `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`,
which is the presentation Stacks 0AJS produces and the only one related to `P`.  The two
inputs are `StacksFrontier/Homology/DoubleHomology.lean`, which computes the homology of a
`double` as the kernel and the cokernel of its one differential, and
`StacksFrontier/RingTheory/NaiveCotangent/PresentationHomology.lean`, which shows both of those
are independent of the presentation.

## Main results

* `Rig.CompletedPolynomialPresentation.annihilator_homology_one_reductionGenerators` and
  `…_zero_reductionGenerators`: the annihilators of the two cohomology modules of
  `NL_{Bₙ/Aₙ}` are the annihilators of `H⁻¹` and `H⁰` of `NL(Bₙ = Aₙ[x]/Jₙ)`.
* `Rig.CompletedPolynomialPresentation.annihilatesCohomology_nl_reductionGenerators_iff`:
  `IᶜBₙ` annihilates the cohomology of `NL(Bₙ = Aₙ[x]/Jₙ)` exactly when every `a ∈ I^c`
  annihilates both cohomology modules of `NL_{Bₙ/Aₙ}` — the elementwise form the source
  uses.
* `Rig.CompletedPolynomialPresentation.exists_annihilatesCohomology_nl_reductionGenerators_iff`:
  the same with the quantifiers `∃ c, ∀ n ≥ 1` in front, which is condition (0AJX) verbatim.

## Implementation notes

Three identifications are needed to read condition (0AJX) off the library's objects; this
file proves the two that do not depend on the geometry, and records what the third is.

*There is no instance diamond here.*
`Rig.AdicFiniteTypeAlgebra.reductionPowAlgebra B n` is `rfl`-equal to the `Algebra (A ⧸ Iⁿ) Bₙ`
instance that typeclass inference already finds, which is Mathlib's
`Ideal.Quotient.algebraQuotientOfLEComap` through
`Ideal.Quotient.algebraQuotientMapQuotient`; so the `letI` that
`Rig.CompletedPolynomialPresentation.reductionGenerators` carries is not needed at the use
site, and `P.reductionGenerators n` can be stated against the ambient instance.  The ideal
of `B` must still be written `(Iⁿ)·B = Rig.AdicFiniteTypeAlgebra.adicIdealPow`, not
`(I·B)ⁿ`, because only that spelling lies over `Iⁿ` by `Ideal.le_comap_map`; the tagged statement
writes it the same way, so `Bₙ` is `B.reductionPow n` on the nose.

*The bridging equalities are stated rather than inlined.*
`NaiveCotangent.H₁ (NL P')` and `LinearMap.ker P'.toExtension.cotangentComplex` are equal by
`rfl`, as are `NaiveCotangent.H₀ (NL P')` and the quotient of the degree-`0` term by the
image of the differential, but the two spellings do not meet inside a rewrite, so
`annihilator_homology_one_reductionGenerators` and `…_zero_reductionGenerators` restate the
results of `StacksFrontier/RingTheory/NaiveCotangent/PresentationHomology.lean` in the `NL` spelling
by `exact` and the main proof rewrites with those.

*What is still missing for `(3) ⇔ (4)` of Tag 0AJU.*  Exactly one statement: that
`Rig.CompletedNaiveCotangentComplex.reducedComplex n` — the quotient of `NL^∧_{B/A}` by the
image of `J ∩ Iⁿ A⟨x⟩` in degree `-1` and by `IⁿB · (⨁ B dxᵢ)` in degree `0`, which is the
object Stacks 0AJS (1) produces and which the
`Rig.CompletedNaiveCotangentComplex.exists_annihilator_twoTerm_iff_forall_reducedComplex`
is stated through — has the same `H⁻¹` and `H⁰` as `NL(P.reductionGenerators n)`.  The route
is a surjective `Aₙ`-algebra map `A⟨x⟩ → Aₙ[x₁, …, x_r]` with kernel `Iⁿ A⟨x⟩`, read as an
`Algebra.Extension.Hom`; in degree `0` the induced map is `⨁ B dxᵢ → ⨁ Bₙ dxᵢ` with kernel
`IⁿB · (⨁ B dxᵢ)` through `Algebra.Generators.cotangentSpaceBasis`, and in degree `-1` it is
`J/J² → Jₙ/Jₙ²` with kernel the image of `J ∩ Iⁿ A⟨x⟩`, the last step being the modular law
`J ⊓ (J² ⊔ Kⁿ) = J² ⊔ (J ⊓ Kⁿ)`.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
-/

@[expose] public section

open Algebra

namespace Rig

namespace CompletedPolynomialPresentation

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I} (P : CompletedPolynomialPresentation I B)

/-- The annihilator of `H⁻¹(NL_{Bₙ/Aₙ})`, taken as the degree-`1` homology of the naive
cotangent complex of the tautological presentation, is the annihilator of `H⁻¹` of the
presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`.  This is presentation independence of `H¹(L)`. -/
public theorem annihilator_homology_one_reductionGenerators (n : ℕ) :
    Module.annihilator (B.reductionPow n)
        ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 1)
      = (NaiveCotangent.H₁ (NaiveCotangent.NL (P.reductionGenerators n))).annihilator :=
  NaiveCotangent.annihilator_homology_one_eq (P.reductionGenerators n)

/-- The annihilator of `H⁰(NL_{Bₙ/Aₙ})`, taken as the degree-`0` homology of the naive
cotangent complex of the tautological presentation, is the annihilator of `H⁰` of the
presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`.  Both cokernels are `Ω[Bₙ⁄Aₙ]`. -/
public theorem annihilator_homology_zero_reductionGenerators (n : ℕ) :
    Module.annihilator (B.reductionPow n)
        ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 0)
      = Module.annihilator (B.reductionPow n)
          (NaiveCotangent.H₀ (NaiveCotangent.NL (P.reductionGenerators n))) :=
  NaiveCotangent.annihilator_homology_zero_eq (P.reductionGenerators n)

/-- **Condition (0AJX) of Stacks 0AJU at one level `n` and one exponent `c`, read off the
presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`.**  The ideal `IᶜBₙ` annihilates both cohomology
modules of `NL(Bₙ = Aₙ[x]/Jₙ)` exactly when every element of `I^c` kills both cohomology
modules of `NL_{Bₙ/Aₙ}` — the source's elementwise condition, phrased through the
*tautological* presentation of `Bₙ` over `Aₙ` and the categorical homology of
`HomologicalComplex.double` in degrees `1` and `0`.

Annihilation is an ideal-theoretic condition, so the elementwise form is recovered by
`Ideal.map_le_iff_le_comap`; the content is presentation independence of the two cohomology
modules. -/
public theorem annihilatesCohomology_nl_reductionGenerators_iff (n c : ℕ) :
    NaiveCotangent.AnnihilatesCohomology ((I ^ c).map (algebraMap A (B.reductionPow n)))
        (NaiveCotangent.NL (P.reductionGenerators n)) ↔
      ∀ a ∈ I ^ c,
        (Ideal.Quotient.mk (B.adicIdealPow n) (algebraMap A B.carrier a) ∈
            Module.annihilator (B.reductionPow n)
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 1) ∧
          Ideal.Quotient.mk (B.adicIdealPow n) (algebraMap A B.carrier a) ∈
            Module.annihilator (B.reductionPow n)
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 0)) := by
  have h₁ := P.annihilator_homology_one_reductionGenerators n
  have h₀ := P.annihilator_homology_zero_reductionGenerators n
  constructor
  · exact fun h a ha => ⟨h₁ ▸ h.hH₁ (Ideal.mem_map_of_mem _ ha),
      h₀ ▸ h.hH₀ (Ideal.mem_map_of_mem _ ha)⟩
  · exact fun h => ⟨Ideal.map_le_iff_le_comap.mpr fun a ha =>
      Ideal.mem_comap.mpr (h₁ ▸ (h a ha).1),
      Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_comap.mpr (h₀ ▸ (h a ha).2)⟩

/-- **Condition (0AJX) of Stacks 0AJU, read off the presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`.**
There is a `c` such that for every `n ≥ 1` the ideal `IᶜBₙ` annihilates both cohomology
modules of `NL(Bₙ = Aₙ[x]/Jₙ)` exactly when there is a `c` such that for every `n ≥ 1` every
element of `I^c` kills both cohomology modules of `NL_{Bₙ/Aₙ}`.

The right-hand side is condition (4) of Stacks 0AJU verbatim: `Bₙ` is
`B.carrier ⧸ (Iⁿ).map (algebraMap A B.carrier)`, the complex is
`Algebra.naiveCotangentComplex (A ⧸ Iⁿ) Bₙ` and the two modules are its homology in degrees
`1` and `0`.  What this does not yet do is compare the left-hand side with
`Rig.CompletedNaiveCotangentComplex.reducedComplex`, through which
`exists_annihilator_twoTerm_iff_forall_reducedComplex` is stated; see the implementation
notes. -/
public theorem exists_annihilatesCohomology_nl_reductionGenerators_iff :
    (∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
        NaiveCotangent.AnnihilatesCohomology ((I ^ c).map (algebraMap A (B.reductionPow n)))
          (NaiveCotangent.NL (P.reductionGenerators n))) ↔
      ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ a ∈ I ^ c,
        (Ideal.Quotient.mk (B.adicIdealPow n) (algebraMap A B.carrier a) ∈
            Module.annihilator (B.reductionPow n)
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 1) ∧
          Ideal.Quotient.mk (B.adicIdealPow n) (algebraMap A B.carrier a) ∈
            Module.annihilator (B.reductionPow n)
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n) (B.reductionPow n)).homology 0)) :=
  ⟨fun ⟨c, hc⟩ => ⟨c, fun n hn =>
      (P.annihilatesCohomology_nl_reductionGenerators_iff n c).mp (hc n hn)⟩,
    fun ⟨c, hc⟩ => ⟨c, fun n hn =>
      (P.annihilatesCohomology_nl_reductionGenerators_iff n c).mpr (hc n hn)⟩⟩

end CompletedPolynomialPresentation

end Rig

end
