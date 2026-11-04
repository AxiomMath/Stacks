module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaBaseCase
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaDeficient
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductCycleAssociativity

/-!
# The Tor formula on two closed subvarieties, in both cases of the dévissage

The dévissage in the proof of Tag 0B0W reduces the Tor formula

`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_n`,  `n = r + s - dim X`,

to the case of the structure sheaves `𝒪_V`, `𝒪_W` of two closed subvarieties of `Supp ℱ` and
`Supp 𝒢`. The source then splits that case in two. If `dim V = r` and `dim W = s` the equality
"is the definition of `V · W`", which against this library's definition is
`Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_structureSheafAt`.
If `dim V < r` or `dim W < s` then `[𝒪_V]_r = 0` or `[𝒪_W]_s = 0`, so the left-hand side
vanishes, and the right-hand side has to be shown to vanish with it — that is
`Stacks.Intersection.ReductionToDiagonal.torSubvarietyProductOfBound_eq_zero_of_lt`, and it is
not a triviality: the source's own footnote takes `r = s = 1`, `X` a nonsingular surface and
`V = W` a closed point, where three `Tor`s are nonzero, of lengths `1, 2, 1`.

This file puts the two cases together, under the source's hypotheses read as conditions on the
points of the two supports and of their intersection.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.torFormula_structureSheafAt` — the Tor formula for
  the structure sheaves of the reduced closures of two points, with no condition on their
  dimensions beyond the source's bounds `dim V ≤ r`, `dim W ≤ s` and `dim (V ∩ W) ≤ n`.

## Implementation notes

Closed subvarieties are their generic points throughout, as cycles are: `V` is the reduced
closure of `x`, and `𝒪_V` is `AlgebraicGeometry.TorFormula.structureSheafAt x`, whose support is
`closure {x}`.

The dimension bounds are stated pointwise, as `∀ w ∈ Supp, relativeDimension w ≤ r`, which is
what `Stacks.Chow.schemeDeltaDimension_reducedSupport_le_iff` says the delta-dimension bound of
`Stacks.Chow.coherentSheafCycle` amounts to, and which is the form that descends to a subsheaf —
that is what the dévissage needs. The relation `r + s = dim X + n` replaces the source's
subtraction `n = r + s - dim X`.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

variable {X : Scheme.{u}}

/-- The cycle of the structure sheaf of the reduced closure of a point in a dimension the closure
does not reach is the zero cycle. -/
theorem coherentSheafCycle_structureSheafAt_eq_zero (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] (x : X) (r : ℤ)
    (hlt : relativeDimension C.dimensionFunction f x < r)
    (hb : schemeDeltaDimension C ((reducedSupport (structureSheafAt x)).subschemeι ≫ f)
      ≤ (r : EInt)) :
    coherentSheafCycle C f (structureSheafAt x) r hb = 0 := by
  refine coherentSheafCycle_eq_zero_of_relativeDimension_ne C f (structureSheafAt x) r hb
    fun w hw => ?_
  rw [supp_structureSheafAt] at hw
  exact ne_of_lt (lt_of_le_of_lt (relativeDimension_le_of_mem_closure C f hw) hlt)

/-- **The Tor formula on the structure sheaves of the reduced closures of two points.** Let `X`
be a nonsingular variety over an algebraically closed field — the chapter convention, Tag 0AZ8 —
of dimension `dX`, let `x`, `y` be points of `X` with reduced closures `V`, `W`, and let
`r + s = dX + n`. Assume `dim V ≤ r`, `dim W ≤ s` and `dim (V ∩ W) ≤ n`. Then

`[𝒪_V]_r · [𝒪_W]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(𝒪_V, 𝒪_W)]_n`.

This is the case the dévissage of Tag 0B0W reduces to, in both of the source's subcases: when
`dim V = r` and `dim W = s` both sides are the alternating sum of Tag 0AZR, and otherwise both
sides vanish. -/
theorem torFormula_structureSheafAt (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] [IsLocallyNoetherian X] (hX : IsRegular X)
    (r s n : ℤ) (dX : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hrs : r + s = (dX : ℤ) + n) (x y : X)
    (hx : ∀ w ∈ SheafOfModules.supp (structureSheafAt x),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r)
    (hy : ∀ w ∈ SheafOfModules.supp (structureSheafAt y),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
    (hxy : ∀ w ∈ SheafOfModules.supp (structureSheafAt x) ∩
        SheafOfModules.supp (structureSheafAt y),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n) :
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (coherentSheafCycle (fieldChowSituation k) f (structureSheafAt x) r
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hx))
        (coherentSheafCycle (fieldChowSituation k) f (structureSheafAt y) s
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hy))
      = intersectionProductCycle (fieldChowSituation k) f hX
          (structureSheafAt x) (structureSheafAt y)
          (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) n
          (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX
            (structureSheafAt x) (structureSheafAt y)
            (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) n hxy) := by
  classical
  let := Classical.decEq X
  have hmem (z : X) : z ∈ SheafOfModules.supp (structureSheafAt z) := by
    rw [supp_structureSheafAt]; exact subset_closure rfl
  have hxx := hx x (hmem x)
  have hyy := hy y (hmem y)
  have hinter : ∀ w ∈ closure ({x} : Set X) ∩ closure ({y} : Set X),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
    intro w hw
    exact hxy w (by rwa [supp_structureSheafAt, supp_structureSheafAt])
  by_cases hxr : relativeDimension (fieldChowSituation k).dimensionFunction f x = r
  · by_cases hys : relativeDimension (fieldChowSituation k).dimensionFunction f y = s
    · -- Both subvarieties have the expected dimension: the source's "definition of `V · W`".
      exact torFormulaCycleIntersectionProduct_structureSheafAt (fieldChowSituation k) f hX x y
        r s n (by rw [schemeDeltaDimension_integralComponentAt, hxr])
        (by rw [schemeDeltaDimension_integralComponentAt, hys]) _ _ _
    · -- `dim W < s`: the cycle `[𝒪_W]_s` vanishes, and so does the alternating sum.
      have hyslt : relativeDimension (fieldChowSituation k).dimensionFunction f y < s :=
        lt_of_le_of_ne hyy hys
      rw [coherentSheafCycle_structureSheafAt_eq_zero (fieldChowSituation k) f y s hyslt]
      refine Eq.trans (cycleIntersectionProduct_zero_right _ _) ?_
      exact (torSubvarietyProductOfBound_eq_zero_of_lt k f hX n x y _ dX hdX hinter
        (by rw [← hrs]; omega)).symm
  · -- `dim V < r`: the cycle `[𝒪_V]_r` vanishes, and so does the alternating sum.
    have hxrlt : relativeDimension (fieldChowSituation k).dimensionFunction f x < r :=
      lt_of_le_of_ne hxx hxr
    rw [coherentSheafCycle_structureSheafAt_eq_zero (fieldChowSituation k) f x r hxrlt]
    refine Eq.trans (cycleIntersectionProduct_zero_left _ _) ?_
    exact (torSubvarietyProductOfBound_eq_zero_of_lt k f hX n x y _ dX hdX hinter
      (by rw [← hrs]; omega)).symm

end Stacks.Intersection.ReductionToDiagonal

end
