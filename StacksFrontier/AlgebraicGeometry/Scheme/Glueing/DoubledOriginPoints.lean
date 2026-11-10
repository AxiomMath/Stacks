module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginSections

/-!
# Points and irreducible closed subsets of affine space with the origin doubled

Affine `n`-space with its origin doubled is covered by two affine charts which agree away from
their origins, so its points are those of affine space together with a second copy of the origin.

In dimension greater than one the scheme has infinitely many irreducible closed subsets which are
closures of nonclosed points: the generic points of the monomial curves `t ↦ (t ^ m, t, 0, …, 0)`
in the first chart have pairwise distinct closures. In every dimension, an irreducible closed
subset other than the two singleton origins contains one origin if and only if it contains the
other.

## Main results

* `AlgebraicGeometry.infinite_irreducibleClosed_closures`: in dimension greater than one there are
  infinitely many irreducible closed subsets that are closures of nonclosed points of the first
  chart.
* `AlgebraicGeometry.mem_origin_iff_mem_origin`: an irreducible closed subset other than the two
  singleton origins contains both origins or neither.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Helpers

private def firstIndex (n : ℕ) (hn : 1 < n) : Fin n :=
  ⟨0, by omega⟩

private def secondIndex (n : ℕ) (hn : 1 < n) : Fin n :=
  ⟨1, by omega⟩

private noncomputable def curveEval (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) (m : ℕ) :
    MvPolynomial (Fin n) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom (algebraMap k (Polynomial k)) (fun i =>
    if i = firstIndex n hn then Polynomial.X ^ m
    else if i = secondIndex n hn then Polynomial.X else 0)

private noncomputable def zeroEval (k : Type u) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)

private noncomputable def curvePoint (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) (m : ℕ) :
    PrimeSpectrum (MvPolynomial (Fin n) k) :=
  ⟨RingHom.ker (curveEval k n hn m), RingHom.ker_isPrime _⟩

private noncomputable def zeroPoint (k : Type u) [Field k] (n : ℕ) :
    PrimeSpectrum (MvPolynomial (Fin n) k) :=
  ⟨RingHom.ker (zeroEval k n), RingHom.ker_isPrime _⟩

private lemma curveEval_comp_zero (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) (m : ℕ)
    (hm : 0 < m) :
    (Polynomial.evalRingHom (0 : k)).comp (curveEval k n hn m) = zeroEval k n := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [curveEval, zeroEval]
  · intro i
    rw [RingHom.comp_apply]
    by_cases h0 : i = firstIndex n hn
    · subst i
      simp [curveEval, zeroEval, firstIndex, secondIndex, Polynomial.evalRingHom,
        Nat.ne_of_gt hm]
    · by_cases h1 : i = secondIndex n hn
      · subst i
        simp [curveEval, zeroEval, firstIndex, secondIndex, Polynomial.evalRingHom]
      · have hi0 : i ≠ ⟨0, by omega⟩ := by simpa [firstIndex] using h0
        have hi1 : i ≠ ⟨1, by omega⟩ := by simpa [secondIndex] using h1
        simp [curveEval, zeroEval, firstIndex, secondIndex, hi0, hi1, Polynomial.evalRingHom]

private lemma curvePoint_not_closed (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) (m : ℕ)
    (hm : 0 < m) :
    ¬ IsClosed ({curvePoint k n hn m} : Set (PrimeSpectrum (MvPolynomial (Fin n) k))) := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  intro hmax
  have hle : (curvePoint k n hn m).asIdeal ≤ (zeroPoint k n).asIdeal := by
    intro p hp
    change zeroEval k n p = 0
    rw [← curveEval_comp_zero k n hn m hm]
    simp [(RingHom.mem_ker).mp hp]
  have hzero_ne_top : (zeroPoint k n).asIdeal ≠ ⊤ := (zeroPoint k n).isPrime.ne_top
  have hXzero : MvPolynomial.X (secondIndex n hn) ∈ (zeroPoint k n).asIdeal := by
    change zeroEval k n (MvPolynomial.X (secondIndex n hn)) = 0
    simp [zeroEval]
  have hXcurve : MvPolynomial.X (secondIndex n hn) ∉ (curvePoint k n hn m).asIdeal := by
    change curveEval k n hn m (MvPolynomial.X (secondIndex n hn)) ≠ 0
    simp [curveEval, firstIndex, secondIndex, Polynomial.X_ne_zero]
  exact hXcurve ((hmax.eq_of_le hzero_ne_top hle) ▸ hXzero)

private noncomputable def curveClosure (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) (m : ℕ) :
    Set (affineSpaceWithDoubledZero k n) :=
  closure ({(chartInclusion k n 0).base (curvePoint k n hn m)} :
    Set (affineSpaceWithDoubledZero k n))

private lemma curveClosure_injective (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) {m l : ℕ}
    (h : curveClosure k n hn (m + 1) = curveClosure k n hn (l + 1)) : m = l := by
  have hle : (curvePoint k n hn (m + 1)).asIdeal ≤ (curvePoint k n hn (l + 1)).asIdeal := by
    refine (PrimeSpectrum.le_iff_specializes _ _).mpr
      ((chartInclusion k n 0).isOpenEmbedding.isInducing.specializes_iff.mp ?_)
    rw [specializes_iff_mem_closure]
    exact (show _ ∈ curveClosure k n hn (m + 1) from h ▸ subset_closure (Set.mem_singleton _))
  have hpoly : MvPolynomial.X (firstIndex n hn) - MvPolynomial.X (secondIndex n hn) ^ (m + 1) ∈
      (curvePoint k n hn (l + 1)).asIdeal :=
    hle (by change curveEval k n hn (m + 1) _ = 0; simp [curveEval, firstIndex, secondIndex])
  have heval : (Polynomial.X : Polynomial k) ^ (l + 1) - Polynomial.X ^ (m + 1) = 0 := by
    change curveEval k n hn (l + 1) _ = 0 at hpoly
    simpa [curveEval, firstIndex, secondIndex] using hpoly
  have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp heval)
  simp only [Polynomial.natDegree_X_pow] at hdeg
  omega

end Helpers

/-- In dimension greater than one, infinitely many irreducible closed subsets of affine space with
doubled origin are closures of nonclosed points in its first affine chart. -/
@[stacks 01JD "many_irreducible_closed"]
theorem infinite_irreducibleClosed_closures (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    Set.Infinite
      { T : Set (affineSpaceWithDoubledZero k n) |
        IsClosed T ∧ IsIrreducible T ∧
          ∃ x : Spec (.of (MvPolynomial (Fin n) k)),
            ¬ IsClosed ({x} : Set (Spec (.of (MvPolynomial (Fin n) k)))) ∧
              T = closure ({(chartInclusion k n 0).base x} :
                Set (affineSpaceWithDoubledZero k n)) } := by
  have hinj : Function.Injective (fun m : ℕ => curveClosure k n hn (m + 1)) :=
    fun _ _ h => curveClosure_injective k n hn h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro T ⟨m, rfl⟩
  exact ⟨isClosed_closure, IsIrreducible.closure isIrreducible_singleton,
    curvePoint k n hn (m + 1), curvePoint_not_closed k n hn (m + 1) (by omega), rfl⟩

section Helpers

private theorem affineOrigin_ideal_eq_span (k : Type u) [Field k] (n : ℕ) :
    (affineOrigin k n).asIdeal =
      Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k)) := by
  change RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) = _
  ext p
  change MvPolynomial.constantCoeff p = 0 ↔
    p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin n → _))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  refine ⟨fun hp m hm => ?_, fun hp => ?_⟩
  · by_contra h
    obtain rfl : m = 0 := Finsupp.ext fun i => by_contra fun hi => h ⟨i, Set.mem_univ i, hi⟩
    exact MvPolynomial.mem_support_iff.mp hm (by simpa [MvPolynomial.constantCoeff] using hp)
  · by_contra hp0
    obtain ⟨i, -, hi⟩ := hp 0 (MvPolynomial.mem_support_iff.mpr
      (by simpa [MvPolynomial.constantCoeff] using hp0))
    exact hi rfl

private theorem affineOrigin_isMaximal (k : Type u) [Field k] (n : ℕ) :
    (affineOrigin k n).asIdeal.IsMaximal := by
  change (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  exact ⟨MvPolynomial.C a, by simp⟩

private theorem affineOrigin_specializes_eq (k : Type u) [Field k] (n : ℕ)
    {y : Spec (.of (MvPolynomial (Fin n) k))} (h : affineOrigin k n ⤳ y) :
    y = affineOrigin k n :=
  PrimeSpectrum.ext ((affineOrigin_isMaximal k n).eq_of_le y.2.ne_top
    ((PrimeSpectrum.le_iff_specializes _ _).2 h)).symm

private theorem mem_punctured_of_ne_origin (k : Type u) [Field k] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) k))) (hne : x ≠ affineOrigin k n) :
    x ∈ puncturedAffineSpace k n := by
  change x ∈ (⨆ i, PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial (Fin n) k))
  by_contra hx
  have hxi : ∀ i : Fin n, MvPolynomial.X i ∈ x.asIdeal := by
    intro i
    by_contra hnot
    exact hx (le_iSup
      (fun j => PrimeSpectrum.basicOpen (MvPolynomial.X j : MvPolynomial (Fin n) k)) i
      ((PrimeSpectrum.mem_basicOpen (MvPolynomial.X i) x).2 hnot))
  have hspan :
      Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k)) ≤ x.asIdeal := by
    rw [Ideal.span_le, Set.range_subset_iff]
    exact hxi
  rw [← affineOrigin_ideal_eq_span k n] at hspan
  have heq : (affineOrigin k n).asIdeal = x.asIdeal :=
    (affineOrigin_isMaximal k n).eq_of_le x.2.ne_top hspan
  exact hne (PrimeSpectrum.ext heq.symm)

private lemma chart_origins_agree_on_punctured (k : Type u) [Field k] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) k)))
    (hx : x ∈ puncturedAffineSpace k n) :
    chartInclusion k n 0 x = chartInclusion k n 1 x := by
  have hij : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by decide
  obtain ⟨y, hy⟩ :
      x ∈ ((doubledZeroGlueData k n).toGlueData.f (ULift.up 0) (ULift.up 1)).opensRange := by
    rw [opensRange_glueData_f k n hij]; exact hx
  refine ((doubledZeroGlueData k n).ι_eq_iff (ULift.up 0) (ULift.up 1) x x).2 ⟨y, hy, ?_⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glueData_t_comp_f k n hij]
  exact hy

private theorem chart_origin_specializes_eq (k : Type u) [Field k] (n : ℕ) (i : Fin 2)
    {y : affineSpaceWithDoubledZero k n}
    (h : chartInclusion k n i (affineOrigin k n) ⤳ y) :
    y = chartInclusion k n i (affineOrigin k n) := by
  obtain ⟨⟨c⟩, z, hz⟩ := (doubledZeroGlueData k n).ι_jointly_surjective y
  by_cases hic : i = c
  · subst c
    obtain rfl : chartInclusion k n i z = y := hz
    rw [affineOrigin_specializes_eq k n
      ((chartInclusion k n i).isOpenEmbedding.isInducing.specializes_iff.mp h)]
  · have hyRange : y ∈ Set.range (chartInclusion k n c) := ⟨z, hz⟩
    have hxiRange : chartInclusion k n i (affineOrigin k n) ∈
        Set.range (chartInclusion k n c) :=
      h.mem_open (chartInclusion k n c).isOpenEmbedding.isOpen_range hyRange
    exact ((origin_notMem_range_other_chart k n i c hic) hxiRange).elim

private theorem chartInclusions_eq_of_mem_punctured (k : Type u) [Field k] (n : ℕ) (i j : Fin 2)
    (hij : i ≠ j) (x : Spec (.of (MvPolynomial (Fin n) k)))
    (hx : x ∈ puncturedAffineSpace k n) :
    chartInclusion k n i x = chartInclusion k n j x := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact chart_origins_agree_on_punctured k n x hx
  · exact (chart_origins_agree_on_punctured k n x hx).symm
  · exact (hij rfl).elim

private theorem origin_mem_of_origin_mem (k : Type u) [Field k] (n : ℕ)
    (T : Set (affineSpaceWithDoubledZero k n)) (hT : IsIrreducible T) (hT_closed : IsClosed T)
    (i j : Fin 2) (hij : i ≠ j)
    (hTi : T ≠ {chartInclusion k n i (affineOrigin k n)})
    (hmem : chartInclusion k n i (affineOrigin k n) ∈ T) :
    chartInclusion k n j (affineOrigin k n) ∈ T := by
  have hxi := hT.isGenericPoint_genericPoint hT_closed
  have hs := hxi.specializes hmem
  obtain ⟨x, hx⟩ : hT.genericPoint ∈ Set.range (chartInclusion k n i) :=
    hs.mem_open (chartInclusion k n i).isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  have hspec : x ⤳ affineOrigin k n :=
    (chartInclusion k n i).isOpenEmbedding.isInducing.specializes_iff.mp (hx ▸ hs)
  by_cases hxo : x = affineOrigin k n
  · subst hxo
    refine absurd (Set.ext fun y =>
      ⟨fun hy => chart_origin_specializes_eq k n i (hx ▸ hxi.specializes hy), ?_⟩) hTi
    rintro rfl
    exact hx ▸ hxi.mem
  · have hxij : hT.genericPoint = chartInclusion k n j x :=
      hx ▸ chartInclusions_eq_of_mem_punctured k n i j hij x (mem_punctured_of_ne_origin k n x hxo)
    exact hxi.specializes_iff_mem.mp (hxij ▸ hspec.map (chartInclusion k n j).continuous)

end Helpers

/-- Apart from the two singleton origins, an irreducible closed subset of affine space with
the origin doubled contains either both origins or neither. -/
@[stacks 01JD "origins_in_closed_subset"]
theorem mem_origin_iff_mem_origin (k : Type u) [Field k] (n : ℕ)
    (T : Set (affineSpaceWithDoubledZero k n))
    (hT : IsIrreducible T) (hT_closed : IsClosed T)
    (hT₀ : T ≠ {chartInclusion k n 0 (affineOrigin k n)})
    (hT₁ : T ≠ {chartInclusion k n 1 (affineOrigin k n)}) :
    (chartInclusion k n 0 (affineOrigin k n) ∈ T ↔
      chartInclusion k n 1 (affineOrigin k n) ∈ T) :=
  ⟨origin_mem_of_origin_mem k n T hT hT_closed 0 1 (by decide) hT₀,
    origin_mem_of_origin_mem k n T hT hT_closed 1 0 (by decide) hT₁⟩

end AlgebraicGeometry

end
