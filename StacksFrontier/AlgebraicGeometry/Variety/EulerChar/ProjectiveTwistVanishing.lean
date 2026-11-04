module

public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Devissage
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist

/-!
# Eventual vanishing of the higher cohomology of the twists of a coherent sheaf

Let `ℱ` be a coherent sheaf on projective space `ℙⁿ` over a field `k`. In each positive degree
`i` the cohomology `Hⁱ(ℙⁿ, ℱ(d))` vanishes for all sufficiently large `d`; this is
[Stacks, Tag 01YS] assertion (4), and once it is available the Hilbert polynomial of `ℱ`
evaluated at a large integer is `dim_k H⁰(ℙⁿ, ℱ(d))`, which is [Stacks, Tag 08AE].

The source proves assertion (4) by descending dévissage on the degree: a coherent sheaf is the
quotient term of a short exact sequence whose middle term is a finite direct sum of twists, the
higher cohomology of such a sum vanishes after a twist, and the long exact sequence moves the
vanishing one degree down. That dévissage is
`exists_isZero_hgroup_projectiveTwist_of_descending_devissage` in the
`Stacks.AlgebraicGeometry.TwistFlatness` namespace; this file discharges every one of its
hypotheses except the dévissage sequence itself, and carries the latter as the hypothesis
`step`.

**No `@[stacks 01YS]` or `@[stacks 08AE]` attribute is attached.** The dévissage sequence of
[Stacks, Tag 01YS] assertion (1) — a surjection onto a coherent sheaf from a finite direct sum of
twists, with coherent kernel — has no declaration in this repository, and neither does the
computation of `Hⁱ(ℙⁿ, 𝒪(d))` of [Stacks, Tag 01XT] that makes the middle term of that sequence
eventually acyclic. Those two are exactly what `step` assumes. Everything else both tags need is
proved here or already in the library: the vanishing bound uniform in the sheaf, the degree
bookkeeping of the dévissage, the quasi-coherence of the twists, and the collapse of the
alternating sum.

## Main results

* `AlgebraicGeometry.exists_isZero_cohomologyOverField_projectiveTwist_of_devissage`:
  [Stacks, Tag 01YS] assertion (4) from the dévissage sequence alone.
* `AlgebraicGeometry.exists_hilbertPolynomial_eval_eq_finrank_zero_of_devissage`: the statement of
  [Stacks, Tag 08AE] from the same hypothesis.

## Implementation notes

The dévissage needs a degree `e` beyond which the cohomology of every twist of every sheaf in the
class vanishes. Projective space over a field is proper over it, so
`AlgebraicGeometry.isZero_cohomologyOverField_of_affineCoverNum_le` supplies `e` as the affine
covering number of `ℙⁿ`, uniformly in the sheaf; the twists are quasi-coherent by
`AlgebraicGeometry.isQuasicoherent_projectiveTwist`, which is the only property of the class of
coherent sheaves that the bound uses.

The dévissage is stated for the abelian-group-valued cohomology `Hgroup`
and the Hilbert polynomial for the `k`-module-valued
`AlgebraicGeometry.cohomologyOverField`; the hypotheses and the conclusion are transported
between the two by `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`, so that
nothing below mentions the abelian-group spelling.

The derived category of a category of module sheaves and of abelian groups is needed only to
build the long exact cohomology sequence inside the dévissage, and neither appears in any
statement here; `CategoryTheory.HasDerivedCategory.standard` supplies both, as in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/Cohomology.lean`.

## References

* [Stacks Project, Tag 08AE](https://stacks.math.columbia.edu/tag/08AE)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.TwistFlatness

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] (n : ℕ)

/-- **[Stacks, Tag 01YS] assertion (4) from its dévissage sequence.** Let `ℱ` be a coherent sheaf
on projective space over a field and let `i` be a positive degree. Suppose every coherent sheaf
`𝒢` is the quotient term of a short exact sequence `0 ⟶ 𝒢' ⟶ ℋ ⟶ 𝒢 ⟶ 0` with `𝒢'` coherent and
with all the higher cohomology of the twists `ℋ(d)` vanishing for `d` large — the content of
[Stacks, Tag 01YS] assertion (1) together with the computation of the cohomology of `𝒪(d)` of
[Stacks, Tag 01XT]. Then `Hⁱ(ℙⁿ, ℱ(d))` vanishes for all `d` large.

The bound in degrees at least the affine covering number of projective space is supplied here and
needs no hypothesis, so the dévissage is run only over the finitely many degrees below it. -/
public theorem exists_isZero_cohomologyOverField_projectiveTwist_of_devissage
    (step : ∀ G : (projectiveSpaceOverRing n (.of k)).Modules, G.IsCoherent →
      ∃ T : ShortComplex (projectiveSpaceOverRing n (.of k)).Modules,
        T.X₃ = G ∧ T.X₁.IsCoherent ∧ T.ShortExact ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
            (projectiveTwist n T.X₂ d) m))
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (i : ℕ) (hi : 0 < i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n F d) i) := by
  obtain ⟨d₀, hd₀⟩ :=
    exists_isZero_hgroup_projectiveTwist_of_descending_devissage
      (R := k) n ⊤ (fun G => G.IsCoherent)
      ((projectiveSpaceOverRing n (.of k)).affineCoverNum ⊤)
      (fun p hp G hG d =>
        have hq : (projectiveTwist n G d).IsQuasicoherent :=
          @isQuasicoherent_projectiveTwist k _ n G (isQuasicoherent_of_isCoherent G) d
        (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ p).1
          (@isZero_cohomologyOverField_of_affineCoverNum_le k _ _
            (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) _
            (projectiveTwist n G d) hq p hp.le))
      (fun G hG => by
        obtain ⟨T, hT₃, hT₁, hTse, d₂, hd₂⟩ := step G hG
        exact ⟨T, hT₃, hT₁, hTse, d₂, fun d hd m hm =>
          (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ m).1 (hd₂ d hd m hm)⟩)
      i hi F ‹F.IsCoherent›
  exact ⟨d₀, fun d hd =>
    (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ i).2 (hd₀ d hd)⟩

/-- **[Stacks, Tag 08AE] from the dévissage sequence of [Stacks, Tag 01YS] assertion (1).** Let
`ℱ` be a coherent sheaf on projective space over a field and let `P` be a rational polynomial
agreeing with the Hilbert polynomial of `ℱ` at every integer. Under the dévissage hypothesis of
`AlgebraicGeometry.exists_isZero_cohomologyOverField_projectiveTwist_of_devissage`, beyond some
twist degree `P(d)` is the dimension over the ground field of the global sections of `ℱ(d)`. -/
public theorem exists_hilbertPolynomial_eval_eq_finrank_zero_of_devissage
    (step : ∀ G : (projectiveSpaceOverRing n (.of k)).Modules, G.IsCoherent →
      ∃ T : ShortComplex (projectiveSpaceOverRing n (.of k)).Modules,
        T.X₃ = G ∧ T.X₁.IsCoherent ∧ T.ShortExact ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
            (projectiveTwist n T.X₂ d) m))
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (P : Polynomial ℚ) (hP : ∀ d : ℤ, P.eval (d : ℚ) = (hilbertPolynomial k n F d : ℚ)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      P.eval (d : ℚ) = (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n F d) 0) : ℚ) :=
  exists_hilbertPolynomial_eval_eq_finrank_zero_of_lt k n F
    (fun i hi _ => exists_isZero_cohomologyOverField_projectiveTwist_of_devissage k n step F i hi)
    P hP

end AlgebraicGeometry

end
