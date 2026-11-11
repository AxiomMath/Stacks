module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts

/-!
# The fibre-dimension bound of Tag 0BV5 for the relative dualizing complex, unconditionally

This file proves [Stacks, Tag 0BV5]: `H^i(f^!𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i` for a morphism
`f : X ⟶ Y` of `FTS S`. The reduction to an affine chart
`Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek` takes the affine-chart
description of `f^!𝒪_Y` at a chart through `x` as input; that description is proved, as
`Stacks.Duality.upperShriekStructureSheafCharts` ([Stacks, Tag 0BV2] for `𝒪_Y`), and the local
dimension `dim_x(X_y)` is a natural number because the fibre is of finite type over a field,
which `StacksFrontier/AlgebraicGeometry/Duality/UpperShriekFibreDimensionFinite.lean` adds.

## Main results

* `Stacks.Duality.exists_chart_presentation` — around every point there is an affine chart with
  a polynomial presentation, inside any neighbourhood.
* `Stacks.Duality.exists_chart_of_upperShriekStructureSheafCharts` — the chart description at a
  chart inside any neighbourhood.
* `Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional` —
  the bound `-d ≤ i` for every natural number `d` equal to `dim_x(X_y)`.

The statement registered as [Stacks, Tag 0BV5], with `dim_x(X_y)` shown to be a natural number, is
`Stacks.Duality.exists_fibreDim_eq_and_neg_le_of_nontrivial_stalk_homology_upperShriek` in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekFibreDimensionFinite.lean`.

## References

* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Around every point of `X` there is an affine chart `U ⊆ f⁻¹(V)` with a polynomial
presentation of `Γ(Y, V) → Γ(X, U)`, inside any given open neighbourhood. -/
theorem exists_chart_presentation (x : X.left) (W : X.left.Opens) (hxW : x ∈ W) :
    ∃ (U : X.left.Opens) (_hU : IsAffineOpen U) (V : Y.left.Opens) (_hV : IsAffineOpen V)
      (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧ U ≤ W ∧
        Nonempty (Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := f.left ⁻¹ᵁ V ⊓ W)
      ⟨hxV, hxW⟩
  have hUV' : U ≤ f.left ⁻¹ᵁ V := hUV.trans inf_le_left
  have := locallyOfFiniteType_left f
  exact ⟨U, hU, V, hV, hUV', hxU, hUV.trans inf_le_right,
    Dualizing.nonempty_polynomialPresentation _ (f.left.finiteType_appLE hV hU hUV')⟩

/-- **The chart description at a chart inside any neighbourhood.** If `f^!𝒪_Y` has the chart
description at every affine chart, then every open neighbourhood of `x` contains an affine chart
through `x` together with a presentation at which the description holds. -/
theorem exists_chart_of_upperShriekStructureSheafCharts (h : UpperShriekStructureSheafCharts f j)
    (x : X.left) (W : X.left.Opens) (hxW : x ∈ W) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens) (_hV : IsAffineOpen V)
      (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧ U ≤ W ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) := by
  obtain ⟨U, hU, V, hV, hUV, hxU, hUW, ⟨p⟩⟩ := exists_chart_presentation f x W hxW
  exact ⟨U, hU, V, hV, hUV, hxU, hUW, p, h V hV U hU hUV p⟩

/-- **The bound of Tag 0BV5 at a named dimension.** For a morphism `f : X ⟶ Y` of `FTS S`,
`x ∈ X` and every natural number `d` equal to the local dimension `dim_x(X_y)` of the fibre,
`H^i(f^!𝒪_Y)_x ≠ 0 ⟹ -d ≤ i`, for every compactification `j` defining `f^!`. The chart
description of `f^!𝒪_Y` is `Stacks.Duality.upperShriekStructureSheafCharts`, and on a chart the
bound is [Stacks, Tag 0E9P]. -/
theorem neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional
    (x : X.left) (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i := by
  obtain ⟨U, hU, V, hV, hUV, hxU, -, he⟩ := exists_chart_of_upperShriekStructureSheafCharts f j
    (upperShriekStructureSheafCharts f j) x ⊤ trivial
  exact neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek f j x
    ⟨U, hU, V, hV, hUV, hxU, he⟩ d hd i hi

end Shriek

end Stacks.Duality

end
