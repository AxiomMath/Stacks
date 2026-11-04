module

public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit

/-!
# The proper-intersection formula for the canonical diagonal class

The canonical family of diagonal classes `Stacks.WeilCohomology.canonicalDiagonalClassFamily`,
the Gysin classes `Δ^!` of Stacks 0FBR, satisfies the proper-intersection formula of Stacks 0FFD
(`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`):
`[V₁]_{n₁} · [V₂]_{n₂} = [V₁ ∩ V₂]_d` for closed subschemes of pure dimension meeting in the
expected dimension with Cohen–Macaulay local rings at the points of dimension `d`.

The class of the family at `W` is `Stacks.Chow.Intersection.diagonalGysinClassOverField`, which
satisfies the conclusion of Stacks 0FEA in every degree
(`Stacks.Chow.Intersection.diagonalGysinClassOverField_capCohenMacaulayFormula`), and the formula
is `Stacks.Chow.Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme`.

## Main results

* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_eq_diagonalGysinClassOverField`: the class
  of the family at `W` is the Gysin class of the diagonal read over the field.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_properIntersectionFormula`: the canonical
  family satisfies the proper-intersection formula.

## References

* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- The class of the canonical family at `W` is the Gysin class of the diagonal of `W ⟶ Spec k`
read for the structure morphisms of the intersection product. -/
theorem canonicalDiagonalClassFamily_eq_diagonalGysinClassOverField {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]
    {n : ℕ} (hn : RelativeDimension sW n) :
    canonicalDiagonalClassFamily k sW n hn = Intersection.diagonalGysinClassOverField k sW hn :=
  rfl

/-- **Stacks 0FFD for the canonical family of diagonal classes.** The Gysin classes `Δ^!` of
Stacks 0FBR satisfy the proper-intersection formula
`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`. -/
theorem canonicalDiagonalClassFamily_properIntersectionFormula :
    DiagonalClassFamily.ProperIntersectionFormula (canonicalDiagonalClassFamily k) := by
  intro W V₁ V₂ sW _ _ _ N hN i₁ _ i₂ _ n₁ n₂ d hd h₁ h₂ h₃ h₄
  exact Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme k
    (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN) i₁ i₂ n₁ n₂ d hd
    (Intersection.diagonalGysinClassOverField_capCohenMacaulayFormula k sW hN (n₁ + n₂))
    h₁ h₂ h₃ h₄

end Stacks.WeilCohomology

end
