module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Step
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.EmbeddingProjectiveSpaceOfModule
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.NegativeDimensionCycles
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.QuasiProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.PrimeCycleMoving

/-!
# Tag 0B1V: the intersection product with a rationally trivial cycle

Let `X` be a nonsingular projective variety over an algebraically closed field `k`, let `α` be an
`r`-cycle and `β` an `s`-cycle on `X` intersecting properly, and assume `α ∼_rat 0`. Then
`α · β ∼_rat 0` (Stacks Project, Tag 0B1V).

The proof follows the source. Embed `X ⊆ 𝐏^N`. By linearity `β = [Z]` is prime, and
`α = ∑ c_i ([W_{i,0}]_r - [W_{i,∞}]_r)`. Induct on the excess of `Z` with respect to the
irreducible components of the fibres `W_{i,0}`, `W_{i,∞}`: when `Z` meets all of them properly,
Tag 0B60 applies; otherwise Tag 0B0E gives a cone `C` with `C · X = [Z] + ∑ m_j [Z_j]` and every
`Z_j` of smaller excess, Tag 0B1T moves `C` to `C'_∞` in a family `C' ⊆ 𝐏^N × ℙ¹`, Tag 0B1M
writes `C · X = ∑ n_k [E_{k,0}]_s`, and Tag 0B60 gives `α · [E_{k,0}] ∼ α · [E_{k,∞}] ∼ 0`.

The argument is carried out for an open subvariety `Y` of a closed subvariety `X̄ ⊆ 𝐏^N`, with `Y`
inside the nonsingular locus of `X̄`; the projective case is `Y = X̄ = X`.

## Main results

In the namespace `Stacks.Intersection.RationalEquivalenceProduct`:

* `torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isOpenImmersion`:
  the statement on an open subvariety `Y` of a closed subvariety of `𝐏^N`.

In the namespace `AlgebraicGeometry.TorFormula`:

* `torFormulaCycleIntersectionProduct_mem_rationalEquivalences`: Tag 0B1V.
* `torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isQuasiProjectiveVariety`:
  Tag 0B1V for a nonsingular quasi-projective variety (Remark 0B61).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (k : Type u) [Field k] [IsAlgClosed k] {Xb : Scheme.{u}} (N : ℕ)
  (iX : Xb ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)) [IsClosedImmersion iX]
  [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))]
  {n : ℕ} (hn : topologicalKrullDim Xb = (n : WithBot ℕ∞))
  {Y : Scheme.{u}} (j₀ : Y ⟶ Xb) [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus Xb)
  (p : Y ⟶ Spec (.of k)) [IsVariety k p]
  (hp : j₀ ≫ iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p) (hY : IsRegular Y)

include hn hU hp in
open scoped Classical in
/-- **Tag 0B1V on an open subvariety of a closed subvariety of `𝐏^N`, in natural degrees.** -/
theorem torFormulaCycleIntersectionProduct_mem_ratCycles_of_isOpenImmersion (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) p r)
    (hα : α ∈ rationalEquivalences (fieldChowSituation k) p r)
    (β : CycleGroup (fieldChowSituation k) p s) (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    torFormulaCycleIntersectionProduct (fieldChowSituation k) p hY ((r : ℤ) + s - n) α.1 β.1 ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : IsVariety k (p ≫ eqToHom (rfl : (fieldChowSituation k).S = Spec (.of k))) := by
    simpa using ‹IsVariety k p›
  -- `Y` has the dimension of `X̄`
  have hdY : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    rcases isEmpty_or_nonempty Y with hY0 | ⟨⟨y₁⟩⟩
    · exact absurd (inferInstance : IrreducibleSpace Y).toNonempty (not_nonempty_iff.mpr hY0)
    have h := ProjectiveSpaceOfModule.topologicalKrullDim_closure_image_of_isOpenImmersion k
      (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) j₀ isClosed_univ
      (IrreducibleSpace.isIrreducible_univ Y)
    have hdense : closure (j₀.base '' (Set.univ : Set Y)) = Set.univ := by
      rw [Set.image_univ]
      exact (j₀.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self y₁⟩).closure_eq
    rw [hdense, topologicalKrullDim_univ, topologicalKrullDim_univ, hn] at h
    exact h.symm
  -- the presentation of `α` by fibre differences (Tag 0AZI)
  obtain ⟨M, cc, δ, hδ, hαeq⟩ :=
    exists_fibreDifferences_sum (fieldChowSituation k) p k rfl (r : ℤ) α hα
  simp only [fibreDifferences, Set.mem_ofPred_eq] at hδ
  choose W hWint hWdim hW0 hWinf hWeq using hδ
  have : ∀ i, IsIntegral (W i).subscheme := hWint
  have hα1 : α.1 = ∑ i, cc i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (zeroFiber p (W i)).subschemeι r).1 -
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p (W i)).subschemeι r).1) := by
    rw [hαeq, AddSubgroup.val_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AddSubgroup.coe_zsmul, hWeq i, AddSubgroup.coe_sub]
  rw [hα1] at hαβ ⊢
  -- by linearity `β` is prime, and then the induction on the excess
  refine torFormulaCycleIntersectionProduct_mem_ratCycles_of_single (fieldChowSituation k) p hY
    ((r : ℤ) + s - n) s _ ?_ β hαβ
  intro z hz hαz
  have hzd : topologicalKrullDim (closure ({z} : Set Y)) = (s : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq k p z, hz, Int.toNat_natCast]
  exact torFormulaCycleIntersectionProduct_single_mem_ratCycles_of_induction
    (fieldChowSituation k) p hY ((r : ℤ) + s - n) n r s _ (fibreComponentSets k p W)
    (fun T hT => (topologicalKrullDim_of_mem_fibreComponentSets hWdim hW0 hWinf hT).le)
    (fun z hz _ hT => torFormulaCycleIntersectionProduct_sum_mem_ratCycles hY n r s hdY W hWdim
      hW0 hWinf cc z hz hT)
    (exists_step k N iX hn j₀ hU p hp hY r s W hWdim hW0 hWinf cc) z hzd hαz

include hn hU hp in
/-- **Tag 0B1V on an open subvariety of a closed subvariety of `𝐏^N`.** Let `X̄ ⊆ 𝐏^N` be a closed
subvariety of dimension `n` and `Y ⊆ X̄` an open subvariety contained in the nonsingular locus of
`X̄`. If `α` is a rationally trivial `r`-cycle on `Y` and `β` an `s`-cycle on `Y` meeting `α`
properly, then `α · β` is a rationally trivial `(r + s - n)`-cycle. -/
theorem torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isOpenImmersion {r s : ℤ}
    (α : CycleGroup (fieldChowSituation k) p r) (β : CycleGroup (fieldChowSituation k) p s)
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hα : α ∈ rationalEquivalences (fieldChowSituation k) p r) :
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) p hY (r + s - n) α.1 β.1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k) p hY
          (r + s - n) α.1 β.1⟩ :
      CycleGroup (fieldChowSituation k) p (r + s - n)) ∈
      rationalEquivalences (fieldChowSituation k) p (r + s - n) := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  by_cases hneg : r < 0 ∨ s < 0
  · have h0 : torFormulaCycleIntersectionProduct (fieldChowSituation k) p hY (r + s - n) α.1 β.1
        = 0 := by
      rcases hneg with hr | hs
      · rw [cycleGroup_eq_zero_of_neg k p hr α]
        exact cycleIntersectionProduct_zero_left _ _
      · rw [cycleGroup_eq_zero_of_neg k p hs β]
        exact cycleIntersectionProduct_zero_right _ _
    convert (rationalEquivalences (fieldChowSituation k) p (r + s - n)).zero_mem using 1
    exact Subtype.ext h0
  obtain ⟨hr, hs⟩ := not_or.mp hneg
  replace hr := not_lt.mp hr
  replace hs := not_lt.mp hs
  obtain ⟨r', rfl⟩ := Int.eq_ofNat_of_zero_le hr
  obtain ⟨s', rfl⟩ := Int.eq_ofNat_of_zero_le hs
  obtain ⟨_, hmem⟩ := (mem_ratCycles_iff (fieldChowSituation k) p _ _).mp
    (torFormulaCycleIntersectionProduct_mem_ratCycles_of_isOpenImmersion k N iX hn j₀ hU p hp hY
      r' s' α hα β hαβ)
  exact hmem

end Stacks.Intersection.RationalEquivalenceProduct

namespace AlgebraicGeometry.TorFormula

/-- **Stacks Project, Tag 0B1V.** Let `X` be a nonsingular projective variety of dimension `n` over
an algebraically closed field `k`. Let `α` be an `r`-cycle and `β` an `s`-cycle on `X` which
intersect properly, so that `α · β` is defined, and assume `α ∼_rat 0`. Then `α · β ∼_rat 0`.

The product is the intersection product of Tag 0B08, an `(r + s - n)`-cycle. -/
@[stacks 0B1V "the whole theorem, for a nonsingular projective variety `X` of dimension `n` over \
an algebraically closed field: for an `r`-cycle `α` and an `s`-cycle `β` meeting properly (Tag \
0AZQ) with `α` rationally equivalent to zero, the Tag 0B08 product `α · β` is a rationally \
trivial `(r + s - n)`-cycle"]
theorem torFormulaCycleIntersectionProduct_mem_rationalEquivalences (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjectiveVariety k p]
    (hX : IsRegular X) {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s : ℤ}
    (α : CycleGroup (fieldChowSituation k) p r) (β : CycleGroup (fieldChowSituation k) p s)
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hα : α ∈ rationalEquivalences (fieldChowSituation k) p r) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX (r + s - n) α.1 β.1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k) p hX
          (r + s - n) α.1 β.1⟩ :
      CycleGroup (fieldChowSituation k) p (r + s - n)) ∈
      rationalEquivalences (fieldChowSituation k) p (r + s - n) := by
  obtain ⟨N, iX, hiX, hiXp, -⟩ :=
    exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjectiveVariety k p
  have := hiX
  have : IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) := by
    rw [hiXp]; infer_instance
  have hU : Set.range (𝟙 X : X ⟶ X).base ⊆ regularLocus X := fun x _ =>
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
  open Stacks.Intersection.RationalEquivalenceProduct in
  exact torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isOpenImmersion
    k N iX hn (𝟙 X) hU p (by rw [Category.id_comp, hiXp]) hX α β hαβ hα

/-- **Stacks Project, Tag 0B61 for Theorem 0B1V.** Let `X` be a nonsingular quasi-projective
variety of dimension `n` over an algebraically closed field `k`. Let `α` be an `r`-cycle and `β`
an `s`-cycle on `X` which intersect properly, and assume `α ∼_rat 0`. Then `α · β ∼_rat 0`.

`X` is an open subscheme of a closed subvariety `X̄ ⊆ 𝐏^N` of the same dimension, inside the
nonsingular locus of `X̄`, and the proof of Tag 0B1V runs on such an open subscheme. -/
@[stacks 0B61 "Theorem 0B1V for a nonsingular quasi-projective variety `X` of dimension `n` over \
an algebraically closed field, which the remark asserts with the same proof: for an `r`-cycle \
`α` and an `s`-cycle `β` meeting properly (Tag 0AZQ) with `α` rationally equivalent to zero, \
the Tag 0B08 product `α · β` is a rationally trivial `(r + s - n)`-cycle. Quasi-projective \
variety is `IsQuasiProjectiveVariety`; the argument is run on `X` as an open subset of the \
nonsingular locus of its closure in projective space, the version of Tag 0B0E the remark \
describes"]
theorem torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isQuasiProjectiveVariety
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsQuasiProjectiveVariety k p] (hX : IsRegular X) {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s : ℤ}
    (α : CycleGroup (fieldChowSituation k) p r) (β : CycleGroup (fieldChowSituation k) p s)
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hα : α ∈ rationalEquivalences (fieldChowSituation k) p r) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX (r + s - n) α.1 β.1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k) p hX
          (r + s - n) α.1 β.1⟩ :
      CycleGroup (fieldChowSituation k) p (r + s - n)) ∈
      rationalEquivalences (fieldChowSituation k) p (r + s - n) := by
  obtain ⟨N, Xb, iX, j₀, hiX, hvar, hj₀, hj₀s, hdim, -⟩ :=
    exists_isOpenImmersion_projectiveSpaceOfModule_of_isQuasiProjectiveVariety k p
  have := hiX
  have := hvar
  have := hj₀
  open Stacks.Intersection.RationalEquivalenceProduct in
  exact torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isOpenImmersion
    k N iX (by rw [hdim, hn]) j₀ (range_subset_regularLocus_of_isRegular j₀ hX) p hj₀s hX α β
    hαβ hα

end AlgebraicGeometry.TorFormula

end
