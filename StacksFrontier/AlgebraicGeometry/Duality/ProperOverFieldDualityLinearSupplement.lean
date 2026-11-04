module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedLinear
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.SectionsOverBaseLinear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualitySupplement

/-!
# Further results on `ProperOverFieldDualityLinear`

Results about the objects of `StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear`
that need imports beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

universe w₁ w₂ u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

end AlgebraicGeometry

end
