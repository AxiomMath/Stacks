module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.PrimeCycleMoving
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.QuasiProjectiveEmbedding

/-!
# The moving lemma

Let `X` be a nonsingular projective variety over an algebraically closed field, let `α` be an
`r`-cycle and `β` an `s`-cycle on `X`. Then there is an `r`-cycle `α'` rationally equivalent to
`α` which intersects `β` properly (Tag 0B1U). By Remark 0B61 the same holds for a nonsingular
quasi-projective variety. Both are proved for finitely many cycles `β i` at once, of arbitrary
dimensions, which is what associativity of the intersection product needs; the single cycle is
the case of a one-element family.

A quasi-projective variety is an open subscheme of a closed subvariety of `𝐏(k^{N+1})`, lying in
the nonsingular locus of the latter when the variety is nonsingular, and the moving lemma on such
an open subset is `AlgebraicGeometry.isMovableOff_of_isOpenImmersion`; see
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.PrimeCycleMoving` for the proof. A
projective variety is quasi-projective.

## Main results

* `exists_rationallyEquivalent_forall_intersectProperly_of_isQuasiProjectiveVariety`:
  **Remark 0B61**, Tag 0B1U for a nonsingular quasi-projective variety and a finite family of
  cycles.
* `exists_rationallyEquivalent_forall_intersectProperly`: **Tag 0B1U**, for a finite family of
  cycles.
* `exists_rationallyEquivalent_intersectProperly`: **Tag 0B1U** as stated.

## References

* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Remark 0B61](https://stacks.math.columbia.edu/tag/0B61)
* [Stacks Project, Tag 04L1](https://stacks.math.columbia.edu/tag/04L1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Chow

universe u

namespace AlgebraicGeometry

/-- **Remark 0B61: the moving lemma for a nonsingular quasi-projective variety, for a finite
family of cycles.** Let `X` be a nonsingular quasi-projective variety over an algebraically closed
field, let `α` be an `r`-cycle on `X` and let `β i` be finitely many cycles on `X`, of dimensions
`s i`. Then there is an `r`-cycle `α'` with `α' ∼_rat α` which intersects every `β i` properly.

`X` is an open subscheme of a closed subvariety `X̄ ⊆ 𝐏(k^{N+1})`
(`exists_isOpenImmersion_projectiveSpaceOfModule_of_isQuasiProjectiveVariety`), contained in the
nonsingular locus of `X̄` because `X` is nonsingular, and the moving lemma on such an open subset
is `isMovableOff_of_isOpenImmersion`. -/
@[stacks 0B61 "Lemma 0B1U for a nonsingular quasi-projective variety, which the remark asserts \
with the same proof; for a finite family of cycles `β i` of arbitrary dimensions `s i` in place \
of a single `s`-cycle, and with `r` and the `s i` arbitrary integers. Nonsingular is \
`IsRegular X`, quasi-projective variety is `IsQuasiProjectiveVariety`, cycles are the graded \
cycle groups `Stacks.Chow.CycleGroup` over `Spec k`, rational equivalence is Tag 02RW and proper \
intersection is Definition 0AZQ. The moving lemma is run on `X` as an open subset of the \
nonsingular locus of its closure in projective space, which is the version of Tag 0B0E the remark \
describes"]
public theorem exists_rationallyEquivalent_forall_intersectProperly_of_isQuasiProjectiveVariety
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsQuasiProjectiveVariety k sX] (hX : IsRegular X) {r : ℤ}
    (α : CycleGroup (fieldChowSituation k) sX r)
    {ι : Type*} [Finite ι] (s : ι → ℤ) (β : ∀ i, CycleGroup (fieldChowSituation k) sX (s i)) :
    ∃ α' : CycleGroup (fieldChowSituation k) sX r,
      RationallyEquivalent (fieldChowSituation k) sX r α' α ∧
        ∀ i, AlgebraicCycle.IntersectProperly α'.1 (β i).1 := by
  obtain ⟨N, Xb, iX, j₀, hiX, hvar, hj₀, hj₀s, hdim, hV⟩ :=
    exists_isOpenImmersion_projectiveSpaceOfModule_of_isQuasiProjectiveVariety k sX
  have := hiX
  have := hvar
  have := hj₀
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k
    (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
  exact isMovableOff_of_isOpenImmersion k (Fin (N + 1) → k) hV iX hn j₀
    (range_subset_regularLocus_of_isRegular j₀ hX) sX hj₀s
    (by rw [← hdim, hn]) (fun i ↦ (β i).1) r α

/-- **Stacks Project, Tag 0B1U, for a finite family of cycles.** Let `X` be a nonsingular
projective variety over an algebraically closed field, let `α` be an `r`-cycle on `X` and let
`β i` be finitely many cycles on `X`, of dimensions `s i`. Then there is an `r`-cycle `α'` with
`α' ∼_rat α` which intersects every `β i` properly. This is the case of
`exists_rationallyEquivalent_forall_intersectProperly_of_isQuasiProjectiveVariety` for a
projective variety. -/
@[stacks 0B1U "for a finite family of cycles `β i` of arbitrary dimensions `s i` in place of the \
single `s`-cycle `β`, which is the case of a one-element family; `r` and the `s i` are arbitrary \
integers. Nonsingular is `IsRegular X`, projective variety is `IsProjectiveVariety`, cycles are \
the graded cycle groups `Stacks.Chow.CycleGroup` over `Spec k`, rational equivalence is Tag \
02RW and proper intersection is Definition 0AZQ. The proof replaces the source's degeneration of \
the cone `C` in `𝐏^N × 𝐏^1` (Tags 0B1T, 0B1M, 0B07) by the flat pullback along the finite \
projection `π : X → 𝐏^n` of the proof of Tag 0B0E, which is flat by miracle flatness, together \
with moving `π(Z)` inside `𝐏^n`"]
public theorem exists_rationallyEquivalent_forall_intersectProperly (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    (hX : IsRegular X) {r : ℤ} (α : CycleGroup (fieldChowSituation k) sX r)
    {ι : Type*} [Finite ι] (s : ι → ℤ) (β : ∀ i, CycleGroup (fieldChowSituation k) sX (s i)) :
    ∃ α' : CycleGroup (fieldChowSituation k) sX r,
      RationallyEquivalent (fieldChowSituation k) sX r α' α ∧
        ∀ i, AlgebraicCycle.IntersectProperly α'.1 (β i).1 := by
  have := IsProjectiveVariety.isQuasiProjectiveVariety k sX
  exact exists_rationallyEquivalent_forall_intersectProperly_of_isQuasiProjectiveVariety k sX hX
    α s β

/-- **Stacks Project, Tag 0B1U.** Let `X` be a nonsingular projective variety over an
algebraically closed field, let `α` be an `r`-cycle and `β` an `s`-cycle on `X`. Then there is an
`r`-cycle `α'` with `α' ∼_rat α` which intersects `β` properly. -/
@[stacks 0B1U "as stated: nonsingular is `IsRegular X`, projective variety is \
`IsProjectiveVariety`, cycles are the graded cycle groups `Stacks.Chow.CycleGroup` over `Spec k`, \
rational equivalence is Tag 02RW and proper intersection is Definition 0AZQ; `r` and `s` are \
arbitrary integers"]
public theorem exists_rationallyEquivalent_intersectProperly (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    (hX : IsRegular X) {r s : ℤ} (α : CycleGroup (fieldChowSituation k) sX r)
    (β : CycleGroup (fieldChowSituation k) sX s) :
    ∃ α' : CycleGroup (fieldChowSituation k) sX r,
      RationallyEquivalent (fieldChowSituation k) sX r α' α ∧
        AlgebraicCycle.IntersectProperly α'.1 β.1 := by
  obtain ⟨α', hα', hp⟩ := exists_rationallyEquivalent_forall_intersectProperly k sX hX α
    (ι := Unit) (fun _ ↦ s) (fun _ ↦ β)
  exact ⟨α', hα', hp ()⟩

end AlgebraicGeometry

end
