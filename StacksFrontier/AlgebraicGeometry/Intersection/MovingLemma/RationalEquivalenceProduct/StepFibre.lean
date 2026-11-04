module

public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepSupport

/-!
# Tag 0B1V: one member of the moved family

In the inductive step of Tag 0B1V the cycle `C · X` is written as `∑ n_k [E_{k,0}]_s` for closed
subvarieties `E_k ⊆ X × ℙ¹` of dimension `s + 1`. For one such `E` whose zero fibre meets the
components of `α` properly and whose infinity fibre meets every component of the fibres in the
presentation of `α` properly, `α · [E_0]_s` is rationally trivial: Tag 0B60 moves it to
`α · [E_∞]_s`, and that product is rationally trivial by the case of proper intersection with the
fibres.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The points `0` and `∞` of `ℙ¹_k` are distinct. -/
theorem zeroLinePoint_ne_infinityLinePoint : zeroLinePoint k ≠ infinityLinePoint k := by
  intro h
  exact Set.disjoint_iff.mp (disjoint_range_lineZeroSection_lineInfinitySection (Spec (.of k)))
    ⟨⟨_, rfl⟩, ⟨IsLocalRing.closedPoint k, h.symm⟩⟩

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

omit [IsAlgClosed k] in
/-- The zero section and the infinity section of `X × ℙ¹` are disjoint. -/
theorem zeroSection_apply_ne_infinitySection_apply (x y : X) :
    (zeroSection p).base x ≠ (infinitySection p).base y := by
  intro h
  have h1 := snd_zeroSection_apply k p x
  rw [h, snd_infinitySection_apply] at h1
  exact zeroLinePoint_ne_infinityLinePoint k h1.symm

omit [IsAlgClosed k] in
/-- A family inside the infinity section has empty zero fibre. -/
theorem coe_support_zeroFiber_eq_empty (E : (projectiveLineProduct p).IdealSheafData)
    (hE : Set.range E.subschemeι ⊆ Set.range (infinitySection p)) :
    ((zeroFiber p E).support : Set X) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  rw [coe_support_zeroFiber, Set.mem_preimage, ← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨y, hy⟩ := hE hx
  exact zeroSection_apply_ne_infinitySection_apply k p x y hy.symm

variable [IsVariety k p] [DecidableEq X] (hX : IsRegular X)

omit [DecidableEq X] in
/-- **The product with a cycle supported on a family of good fibre components.** If every point
of the support of an `s`-cycle `γ` has closure contained in a closed set `F` meeting every
component of the fibres of the presentation properly, then `α · γ` is rationally trivial. -/
theorem torFormulaCycleIntersectionProduct_mem_ratCycles_of_support (n r s : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {ι : Type*} [Fintype ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) [∀ i, IsIntegral (W i).subscheme]
    (hDim : ∀ i, ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 = r + 1)
    (h₀ : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (infinitySection p))
    (c : ι → ℤ) (F : Set X)
    (hF : ∀ A ∈ fibreComponentSets k p W,
      topologicalKrullDim ↥(F ∩ A) + (n : WithBot ℕ∞) ≤ ((s + r : ℕ) : WithBot ℕ∞))
    (γ : CycleGroup (fieldChowSituation k) p (s : ℤ))
    (hγ : ∀ t, γ.1 t ≠ 0 → closure ({t} : Set X) ⊆ F) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
        (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1)) γ.1 ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
  classical
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hfin := finite_support_of_compactSpace γ.1
  rw [AlgebraicCycle.eq_sum_zsmul_single hfin]
  change cycleIntersectionProductRightHom (torFormulaSubvarietyProductTotal (fieldChowSituation k)
    p hX ((r : ℤ) + s - n)) _ _ ∈ _
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun t ht => ?_
  have ht' : γ.1 t ≠ 0 := hfin.mem_toFinset.mp ht
  rw [map_zsmul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hrel : relativeDimension (fieldChowSituation k).dimensionFunction p t = s :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) p s γ.1).mp γ.2 t ht'
  have hz : topologicalKrullDim (closure ({t} : Set X)) = (s : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_eq_toNat_relativeDimension k p t, hrel, Int.toNat_natCast]
  exact torFormulaCycleIntersectionProduct_sum_mem_ratCycles hX n r s hn W hDim h₀ hInf c t hz
    fun A hA => le_trans (add_le_add_left (topologicalKrullDim_le_of_subset
      (Set.inter_subset_inter_left _ (hγ t ht'))) _) (hF A hA)

omit [DecidableEq X] in
/-- **Tag 0B1V, one member of the moved family.** Let `α = ∑ c_i ([W_{i,0}]_r - [W_{i,∞}]_r)` and
let `E ⊆ X × ℙ¹` be integral of dimension `s + 1`, not contained in the zero section, such that
`E_0` meets the closure of every point of the support of `α` properly and `E_∞` meets every
component of the fibres `W_{i,0}`, `W_{i,∞}` properly. Then `α · [E_0]_s` is rationally trivial. -/
theorem torFormulaCycleIntersectionProduct_zeroFiber_mem_ratCycles (n r s : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {ι : Type*} [Fintype ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) [∀ i, IsIntegral (W i).subscheme]
    (hDim : ∀ i, ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 = r + 1)
    (h₀ : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (infinitySection p))
    (c : ι → ℤ)
    (E : (projectiveLineProduct p).IdealSheafData) [IsIntegral E.subscheme]
    (hDimE : ∀ ξ : genericPoints E.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p E) ξ.1 = s + 1)
    (h₀E : ¬ Set.range E.subschemeι ⊆ Set.range (zeroSection p))
    (ha : ∀ x : X, (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1)) x ≠ 0 →
      topologicalKrullDim ↥(closure ({x} : Set X) ∩ ((zeroFiber p E).support : Set X)) +
        (n : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞))
    (hb : ∀ A ∈ fibreComponentSets k p W,
      topologicalKrullDim ↥(((infinityFiber p E).support : Set X) ∩ A) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞)) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
        (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1))
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (zeroFiber p E).subschemeι s).1 ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
  classical
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  by_cases hIE : Set.range E.subschemeι ⊆ Set.range (infinitySection p)
  · rw [cycleAssociatedToClosedSubscheme_eq_zero_of_support_eq_empty k p _
      (coe_support_zeroFiber_eq_empty k p E hIE)]
    change cycleIntersectionProduct _ _ 0 ∈ _
    rw [cycleIntersectionProduct_zero_right]
    exact AddSubgroup.zero_mem _
  -- the product with the infinity fibre
  have hinf := torFormulaCycleIntersectionProduct_mem_ratCycles_of_support k p hX n r s hn W hDim
    h₀ hInf c _ hb (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (infinityFiber p E).subschemeι s) fun t ht =>
        subset_of_mem_componentSets
          (closure_mem_componentSets_of_cycle_ne_zero (fieldChowSituation k) p _ _ ht)
  -- the difference of the two fibres, by Tag 0B60 at each point of the support of `α`
  have hdiff : torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
      (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1))
      ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (zeroFiber p E).subschemeι s).1 -
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (infinityFiber p E).subschemeι s).1) ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
    have hfin := finite_support_of_compactSpace (∑ i, c i •
      ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1))
    change cycleIntersectionProductLeftHom (torFormulaSubvarietyProductTotal (fieldChowSituation k)
      p hX ((r : ℤ) + s - n)) _ _ ∈ _
    rw [AlgebraicCycle.eq_sum_zsmul_single hfin, map_sum]
    refine AddSubgroup.sum_mem _ fun x hx => ?_
    have hx' := hfin.mem_toFinset.mp hx
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ _
    have hmem := closure_mem_fibreComponentSets_of_ne_zero k p W c r hx'
    have hxd := topologicalKrullDim_of_mem_fibreComponentSets hDim h₀ hInf hmem
    have hpInf : topologicalKrullDim
        ↥(closure ({x} : Set X) ∩ ((infinityFiber p E).support : Set X)) +
        (n : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
      rw [Set.inter_comm, Nat.add_comm]
      exact hb _ hmem
    have h := torFormulaCycleIntersectionProduct_fibreDifference_mem_ratCycles k p hX n s r hn E
      hDimE h₀E hIE x hxd (ha x hx') hpInf
    have hdeg : ((s : ℤ) + r - n) = ((r : ℤ) + s - n) := by ring
    rw [hdeg] at h
    change torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
      (Function.locallyFinsuppWithin.single x 1) _ ∈ _
    rw [torFormulaCycleIntersectionProduct_comm]
    exact h
  have hsplit : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (zeroFiber p E).subschemeι s).1 =
      ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (zeroFiber p E).subschemeι s).1 -
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (infinityFiber p E).subschemeι s).1) +
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (infinityFiber p E).subschemeι s).1 := (sub_add_cancel _ _).symm
  rw [hsplit]
  change cycleIntersectionProductRightHom (torFormulaSubvarietyProductTotal (fieldChowSituation k)
    p hX ((r : ℤ) + s - n)) _ (_ + _) ∈ _
  rw [map_add]
  exact AddSubgroup.add_mem _ hdiff hinf

end Stacks.Intersection.RationalEquivalenceProduct

end
