module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafSymmetry

/-!
# Commutativity of the intersection product of cycles

The intersection product of cycles of Tag 0B08 is the bilinear extension of the Section 43.14
product `W · V = ∑ᵢ (-1)ⁱ [Torᵢ(𝒪_W, 𝒪_V)]` of two closed subvarieties. The two `Tor` sheaves of
a pair of modules have the same support and the same lengths, so that product is symmetric, and
hence so is its bilinear extension: `α · β = β · α`. The source calls this clear (Section 43.21,
Tag 0B0G).

## Main results

* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_comm_of_symm`: the bilinear extension of
  a symmetric product is commutative.
* `AlgebraicGeometry.TorFormula.torSupportBound_comm`,
  `AlgebraicGeometry.TorFormula.torFormulaSubvarietyProductTotal_comm`: the product of two closed
  subvarieties is symmetric.
* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_comm`: `α · β = β · α`.

## References

* [Stacks Project, Tag 0B0G](https://stacks.math.columbia.edu/tag/0B0G)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
-/

@[expose] public section

namespace AlgebraicGeometry.TorFormula

universe u

variable {X : Scheme.{u}}

/-- The bilinear extension of a symmetric product of closed subvarieties is commutative. -/
theorem cycleIntersectionProduct_comm_of_symm [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (hprod : ∀ x y, prod x y = prod y x)
    (α β : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod α β = cycleIntersectionProduct prod β α := by
  have hα := finite_support_of_compactSpace α
  have hβ := finite_support_of_compactSpace β
  rw [cycleIntersectionProduct_eq_sum prod hα hβ, cycleIntersectionProduct_eq_sum prod hβ hα,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm, hprod]

variable (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [IsLocallyNoetherian X] (hX : IsRegular X)

/-- The delta-dimension bound for the `Tor` sheaves of two points is symmetric in the points: the
two `Tor` sheaves have the same reduced support. -/
theorem torSupportBound_comm (k : ℤ) (x y : X) :
    TorSupportBound C f hX k x y ↔ TorSupportBound C f hX k y x := by
  have key : ∀ a b : X, TorSupportBound C f hX k a b → TorSupportBound C f hX k b a := by
    intro a b h i
    have := isCoherent_torSheaf_of_isRegular X hX _ _ (isCoherent_structureSheafAt a)
      (isCoherent_structureSheafAt b) i
    have := isCoherent_torSheaf_of_isRegular X hX _ _ (isCoherent_structureSheafAt b)
      (isCoherent_structureSheafAt a) i
    have e := reducedSupport_torSheaf_comm (structureSheafAt a) (structureSheafAt b) i
    convert h i using 3 <;>
      first
      | exact e.symm
      | exact congr_arg_heq (fun J : X.IdealSheafData => J.subschemeι) e.symm
  exact ⟨key x y, key y x⟩

/-- The Section 43.14 product of two closed subvarieties is symmetric. -/
theorem torFormulaSubvarietyProductTotal_comm (k : ℤ) (x y : X) :
    torFormulaSubvarietyProductTotal C f hX k x y =
      torFormulaSubvarietyProductTotal C f hX k y x := by
  by_cases h : TorSupportBound C f hX k x y
  · rw [torFormulaSubvarietyProductTotal_eq_of_bound C f hX k h,
      torFormulaSubvarietyProductTotal_eq_of_bound C f hX k
        ((torSupportBound_comm C f hX k x y).1 h)]
    exact intersectionProductCycle_comm C f hX _ _ _ _ k _ _
  · rw [torFormulaSubvarietyProductTotal_eq_zero C f hX k h,
      torFormulaSubvarietyProductTotal_eq_zero C f hX k
        (fun h' => h ((torSupportBound_comm C f hX k x y).2 h'))]

/-- **The intersection product of cycles is commutative**: `α · β = β · α`. On a quasi-compact
scheme — in particular on a variety — every cycle has finitely many components, which is what
the bilinear expansion uses. -/
theorem torFormulaCycleIntersectionProduct_comm [CompactSpace X] (k : ℤ)
    (α β : AlgebraicCycle X ℤ) :
    torFormulaCycleIntersectionProduct C f hX k α β =
      torFormulaCycleIntersectionProduct C f hX k β α :=
  cycleIntersectionProduct_comm_of_symm _ (torFormulaSubvarietyProductTotal_comm C f hX k) α β

end AlgebraicGeometry.TorFormula

end
