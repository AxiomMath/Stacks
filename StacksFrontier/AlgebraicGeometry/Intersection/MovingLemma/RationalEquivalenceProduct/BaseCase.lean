module

public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Reduction
public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Sections
public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.FibreComponents
public import StacksFrontier.AlgebraicGeometry.Intersection.RationalEquivalence.FibreSpecialCase
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProductComm

/-!
# Tag 0B1V: the case of proper intersection with the fibres

Let `X` be a nonsingular variety of dimension `n` over an algebraically closed field and
`W ⊆ X × ℙ¹` an integral closed subscheme of dimension `r + 1` contained in neither section, so
that `[W₀]_r - [W_∞]_r` is one of the basic rationally trivial `r`-cycles. If a closed
subvariety `Z = closure {z}` of dimension `s` meets both fibres `W₀` and `W_∞` properly, then
`([W₀]_r - [W_∞]_r) · [Z]` is rationally equivalent to zero. This is Tag 0B60 applied to `W` and
`Z`, read through the commutativity of the intersection product; when `W` does not dominate `ℙ¹`
both fibres are empty and there is nothing to prove.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [IsVariety k p] [DecidableEq X] (hX : IsRegular X)

omit [IsAlgClosed k] [DecidableEq X] in
/-- The cycle of a closed subscheme with empty support is zero. -/
theorem cycleAssociatedToClosedSubscheme_eq_zero_of_support_eq_empty (D : X.IdealSheafData)
    (hD : (D.support : Set X) = ∅) (m : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) p D.subschemeι m = 0 := by
  have : IsEmpty D.subscheme := ⟨fun y => by
    have : D.subschemeι.base y ∈ (D.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self y
    rw [hD] at this
    exact this⟩
  exact cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty (fieldChowSituation k) p D.subschemeι m

omit [IsAlgClosed k] [DecidableEq X] in
/-- The dimension of an integral member of the family from its relative dimension. -/
theorem topologicalKrullDim_support_of_relativeDimension
    (W : (projectiveLineProduct p).IdealSheafData)
    [IsIntegral W.subscheme] {r : ℕ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1) :
    topologicalKrullDim (W.support : Set (projectiveLineProduct p)) =
      ((r + 1 : ℕ) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_support_eq, ← topologicalKrullDim_univ,
    ← genericPoint_closure W.subscheme,
    topologicalKrullDim_closure_eq_toNat_relativeDimension k (familyBase p W),
    hDim ⟨genericPoint W.subscheme, genericPoint_mem_genericPoints W.subscheme⟩]
  norm_cast

/-- **Tag 0B1V, the case of proper intersection with the fibres.** For `W ⊆ X × ℙ¹` integral of
dimension `r + 1` and contained in neither section, and `Z = closure {z}` of dimension `s` meeting
the fibres `W₀` and `W_∞` properly, the product `([W₀]_r - [W_∞]_r) · [Z]` is rationally
equivalent to zero. -/
theorem torFormulaCycleIntersectionProduct_fibreDifference_mem_ratCycles (n r s : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (z : X) (hz : topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞))
    (hp₀ : topologicalKrullDim ↥(closure ({z} : Set X) ∩ ((zeroFiber p W).support : Set X)) +
      (n : WithBot ℕ∞) ≤ ((s + r : ℕ) : WithBot ℕ∞))
    (hpInf : topologicalKrullDim
        ↥(closure ({z} : Set X) ∩ ((infinityFiber p W).support : Set X)) +
      (n : WithBot ℕ∞) ≤ ((s + r : ℕ) : WithBot ℕ∞)) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
        ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p W).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p W).subschemeι r).1)
        (Function.locallyFinsuppWithin.single z 1) ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hsub : ∀ A B : AlgebraicCycle X ℤ,
      torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n) (A - B)
        (Function.locallyFinsuppWithin.single z 1) =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n) A
          (Function.locallyFinsuppWithin.single z 1) -
        torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n) B
          (Function.locallyFinsuppWithin.single z 1) := fun A B =>
    (cycleIntersectionProductLeftHom (torFormulaSubvarietyProductTotal (fieldChowSituation k) p hX
      ((r : ℤ) + s - n)) (Function.locallyFinsuppWithin.single z 1)).map_sub A B
  by_cases hdom : IsDominant (W.subschemeι ≫
      pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))
  · have := hdom
    have h :=
      Stacks.Intersection.RationalEquivalence.rationallyEquivalent_intersectionProduct_fibreCycle
        k p hX n s r hn W (topologicalKrullDim_support_of_relativeDimension k p W hDim)
        (zeroLinePoint k) (infinityLinePoint k) (isClosed_zeroLinePoint k)
        (isClosed_infinityLinePoint k) z hz
        (by rwa [closedPointSection_zeroLinePoint, Scheme.IdealSheafData.range_subschemeι])
        (by rwa [closedPointSection_infinityLinePoint, Scheme.IdealSheafData.range_subschemeι])
    have hmem := mem_ratCycles_of_mem (fieldChowSituation k) p _ _ h
    simp only [AddSubgroup.coe_sub] at hmem
    rw [closedPointSection_zeroLinePoint, closedPointSection_infinityLinePoint] at hmem
    have hdeg : ((s : ℤ) + r - n) = ((r : ℤ) + s - n) := by ring
    rw [hdeg] at hmem
    rw [hsub, torFormulaCycleIntersectionProduct_comm, torFormulaCycleIntersectionProduct_comm
      (fieldChowSituation k) p hX _ (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p W).subschemeι r).1]
    exact hmem
  · have h0e : ((zeroFiber p W).support : Set X) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp fun hne =>
        hdom (isDominant_of_zeroFiber_nonempty k p W h₀ hne)
    have hie : ((infinityFiber p W).support : Set X) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp fun hne =>
        hdom (isDominant_of_infinityFiber_nonempty k p W hInf hne)
    rw [cycleAssociatedToClosedSubscheme_eq_zero_of_support_eq_empty k p _ h0e,
      cycleAssociatedToClosedSubscheme_eq_zero_of_support_eq_empty k p _ hie, sub_self]
    show cycleIntersectionProduct _ 0 _ ∈ _
    rw [cycleIntersectionProduct_zero_left]
    exact AddSubgroup.zero_mem _

end Stacks.Intersection.RationalEquivalenceProduct

end
