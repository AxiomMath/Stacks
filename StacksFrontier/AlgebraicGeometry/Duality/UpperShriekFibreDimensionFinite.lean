module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus

/-!
# Tag 0BV5: the relative dualizing complex vanishes below minus the fibre dimension

Let `S` be a Noetherian scheme, `f : X ⟶ Y` a morphism of `AlgebraicGeometry.FTS S` and `x ∈ X`
with image `y ∈ Y`. This file proves [Stacks, Tag 0BV5]:

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i`.

The local dimension `dim_x(X_y)` is a natural number, because on an affine chart it is the
relative dimension of a finite type algebra (`Algebra.exists_relativeDimensionAt_eq_natCast`),
and the bound at that number is
`Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional`.

## Main results

* `Stacks.Duality.exists_fibreDim_eq_and_neg_le_of_nontrivial_stalk_homology_upperShriek` —
  **[Stacks, Tag 0BV5]**.

## References

* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u

namespace Stacks.Duality

open DerivedPushforward

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0BV5 (Lemma 48.21.3).** In Situation 48.16.1 let `f : X ⟶ Y` be a
morphism of `FTS S` and let `x ∈ X` with image `y ∈ Y`. Then

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i`,

for every compactification `j` defining `f^!`. The local dimension `dim_x(X_y)` of the fibre
(`topologicalKrullDimAt` of the scheme-theoretic fibre at `x`) is a natural number `d`, since the
fibre is of finite type over the residue field of `y`, and the conclusion is `-d ≤ i`. -/
@[stacks 0BV5 "f^! is Stacks.Duality.upperShriek of any compactification j; O_Y is \
  DerivedPushforward.derivedStructureSheaf; H^i(-)_x ≠ 0 is Nontrivial on the stalk at x of the \
  i-th cohomology sheaf; dim_x(X_y) is topologicalKrullDimAt of the scheme-theoretic fibre at x, \
  shown to be a natural number d, and the conclusion is -d ≤ i"]
theorem exists_fibreDim_eq_and_neg_le_of_nontrivial_stalk_homology_upperShriek
    (x : X.left) (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    ∃ d : ℕ, topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞) ∧ -(d : ℤ) ≤ i := by
  obtain ⟨U, hU, V, hV, hUV, hxU, -, -⟩ := exists_chart_presentation f x ⊤ trivial
  have := locallyOfFiniteType_left f
  let _ : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y.left, V) Γ(X.left, U) := f.left.finiteType_appLE hV hU hUV
  obtain ⟨d, hd⟩ := Algebra.exists_relativeDimensionAt_eq_natCast Γ(Y.left, V)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hd' : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞) := by
    rw [Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV x hxU, hd]
  exact ⟨d, hd', neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional f j x d
    hd' i hi⟩

end Shriek

end Stacks.Duality

end
