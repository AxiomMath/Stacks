module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyProper
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
# Smooth projective curves of genus one exist over every field

The plane cubic `projOf C` of an elliptic Weierstrass curve `C` over a field `k` is a smooth
projective curve of genus one over `k`. Smoothness is
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.smoothOfRelativeDimension_projectionOf`. The
genus is `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.genus_projectionOf`. Being a curve is
`AlgebraicGeometry.GenusOne.isCurve`, and projectivity is [Stacks, Tag 0A26]. Every field carries
an elliptic Weierstrass curve, `WeierstrassCurve.ofJ 0`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isCurve_projectionOf`,
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isProjectiveVariety_projectionOf`.
* `AlgebraicGeometry.GenusOne.exists_smooth_projective_curve_genus_one`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

variable {k : Type u} [Field k] (C : WeierstrassCurve k) [C.IsElliptic]

/-- The plane cubic of an elliptic curve over a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_projectionOf_of_isElliptic :
    SmoothOfRelativeDimension 1 (projectionOf C) :=
  smoothOfRelativeDimension_projectionOf C C.isUnit_Δ

/-- The plane cubic of an elliptic curve over a field is a curve. -/
theorem isCurve_projectionOf : IsCurve k (projectionOf C) :=
  have := smoothOfRelativeDimension_projectionOf_of_isElliptic C
  GenusOne.isCurve (projectionOf C) (finrank_structureSheafCohomology_projectionOf_zero C)

/-- The plane cubic of an elliptic curve over a field is a projective variety. -/
theorem isProjectiveVariety_projectionOf : IsProjectiveVariety k (projectionOf C) :=
  have := isCurve_projectionOf C
  { isProjective :=
  Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
      (projectionOf C) (IsCurve.topologicalKrullDim_eq_one (k := k) (f := projectionOf C)).le }

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

namespace AlgebraicGeometry.GenusOne

open ModuliEllipticCurves.Weierstrass in
/-- **Over every field there is a smooth projective curve of genus one**: the plane cubic of an
elliptic Weierstrass curve. -/
theorem exists_smooth_projective_curve_genus_one (k : Type u) [Field k] :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ Spec (.of k)), IsCurve k f ∧ IsProjectiveVariety k f ∧
      Smooth f ∧ genus f = 1 := by
  classical
  let C := WeierstrassCurve.ofJ (0 : k)
  have := smoothOfRelativeDimension_projectionOf_of_isElliptic C
  exact ⟨projOf C, projectionOf C, isCurve_projectionOf C, isProjectiveVariety_projectionOf C,
    SmoothOfRelativeDimension.smooth 1 _, genus_projectionOf C⟩

end AlgebraicGeometry.GenusOne

end
