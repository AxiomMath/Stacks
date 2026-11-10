module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing

/-!
# The trace formula for the powers of Frobenius

Let `X` be a separated scheme of finite type over a finite field `k`, `k̄` an algebraic closure of
`k` and `F` an ℓ-adic sheaf on `X`. The trace formula of [Stacks, Tag 03V2] for
`X_N = X ×_k k_N` over the subfield `k_N ⊆ k̄` of degree `N` over `k` is the identity

`∑_{deg x ∣ N} deg x · Tr((π_x^*)^{N / deg x} | F_x̄) = ∑_i (-1)^i Tr((π_X^*)^N | Hⁱ_c(X_k̄, F))`,

the identity displayed in the proof of [Stacks, Tag 03V0] before the Möbius inversion. This file
deduces it from the trace formula over the finite extensions of `k` inside `k̄`, as in the source.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_pow_eq_of_traceFormula`
* `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_pow_eq_sum_range_three`: on a smooth curve the
  alternating sum runs over `i ∈ {0, 1, 2}`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **The trace formula for `(π_X^*)^N` from the trace formula over the finite extensions.** Let
`F` be an ℓ-adic sheaf on a separated scheme `X` of finite type over a finite field `k` with
`p ^ q` elements, and `k̄` an algebraic closure of `k`. Suppose that for every finite extension
`k ⊆ k' ⊆ k̄`, with `p ^ q'` elements, the trace formula of [Stacks, Tag 03V2] holds for
`X' = X ×_k k'` and the restriction of `F` (`htr`). Then for every `N ≥ 1`, the sum
`∑_{deg x ∣ N} deg x · Tr((π_x^*)^{N / deg x} | F_x̄)` equals
`∑_i (-1)^i Tr((π_X^*)^N | Hⁱ_c(X_k̄, F))`. -/
theorem LAdicSheaf.finsum_trace_pow_eq_of_traceFormula (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (htr : ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
      [Algebra k' kbar] [IsScalarTower k k' kbar] [CharP k' p]
      [IsNoetherian (fieldExtensionScheme B X f k').1] (q' : ℕ)
      (hcard' : Fintype.card k' = p ^ q'),
      ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
          (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
          LinearMap.trace ℚ_[ℓ] _
            (LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
              (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) y.1
              (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2)) =
        ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
            (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f j k') kbar p q' hcard'
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom)
    (N : ℕ) (hN : N ≠ 0) :
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ N),
        (residueDegree f x.1 : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
            (N / residueDegree f x.1)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          i).hom ^ N) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := Nat.exists_eq_succ_of_ne_zero hN
  obtain ⟨K, hKfin, hK⟩ := exists_intermediateField_finrank_eq k kbar p (m + 1)
  let : Fintype K := @Fintype.ofFinite _ (Module.finite_of_finite k)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have := isNoetherian_fieldExtensionScheme B X f K
  have hcard' : Fintype.card K = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := K), hK, hcard, pow_mul]
  rw [← LAdicSheaf.finsum_rationalStalkFrobenius_fieldExtension B X ℓ f K F (m + 1) hK hN,
    htr K (q * (m + 1)) hcard']
  refine finsum_congr fun i => ?_
  congr 1
  exact LAdicSheaf.trace_rationalGeometricCompactlySupportedFrobenius_fieldExtension B X ℓ f j K
    kbar F i p q hcard m hcard'

section Curve

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **On a smooth curve the alternating sum of traces runs over `i ∈ {0, 1, 2}`**: for `X` smooth
of relative dimension one over `k` and `k̄` an algebraic closure of `k`, `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)`
vanishes for `i < 0` and for `i > 2`. -/
theorem LAdicSheaf.finsum_trace_pow_eq_sum_range_three [SmoothOfRelativeDimension 1 f]
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          i).hom ^ N) =
      ∑ i ∈ Finset.range 3, (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          (i : ℤ)).hom ^ N) := by
  have hz : ∀ i : ℤ, (i < 0 ∨ 2 < i) → LinearMap.trace ℚ_[ℓ] _
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom ^ N) = 0 := by
    intro i hi
    have : Subsingleton
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
      rcases hi with h | h
      · exact ModuleCat.subsingleton_of_isZero
          (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B X ℓ f j kbar
            F i h)
      · exact LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt B X
          ℓ f j kbar F i h
    rw [Subsingleton.elim ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar
      p q hcard F i).hom ^ N) 0, map_zero]
  have hs : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 2) ?_]
  · rw [hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [add_assoc]
    rfl
  · intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra h
    exact hi (by rw [hz i (by omega), mul_zero])

end Curve

end Stacks.EtaleCohomology

end
