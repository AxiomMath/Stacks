module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealArbitraryField
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected

/-!
# The residue field at a closed point as an extension of the ground field

Let `k` be a field and `X` a scheme locally of finite type over `k`.  At a closed point `x` the
residue field `κ(x)` is a finite extension of `k`, and the ground field, the residue field of the
image point in `Spec k` and `κ(x)` form a tower.  These are the translations between the two
spellings of "an extension of the ground field" — over `k` directly, and over `κ(f x)` in the
spelling of Tag 02G8 — that the Tag 0C4E material needs.

## Main results

* `AlgebraicGeometry.fieldToResidue_comp` — the ground-field map to a residue field is
  functorial in the scheme.
* `Stacks.Curves.module_finite_fieldToResidue` — the residue field at a closed point of a scheme
  locally of finite type over a field is a finite extension of that field.
* `Stacks.Curves.isScalarTower_residueField` — the ground field, the residue field of the image
  point in `Spec k` and the residue field at the point form a tower.

## Implementation notes

The two fields `k` and `κ(f x)` are identified by `AlgebraicGeometry.specFieldResidueIso`, and
`AlgebraicGeometry.fieldToResidue_eq_residueFieldMap` makes `k ⟶ κ(f x) ⟶ κ(x)` a tower, so
separability and finiteness pass from the bottom to the top of it.  Transport along a subscheme
inclusion, whose residue field map is an isomorphism because the inclusion is surjective on
stalks, carries the ground-field maps to each other by `AlgebraicGeometry.fieldToResidue_comp`.

## References

* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The ground-field map to a residue field is functorial.**  For `i : Z ⟶ X` over `Spec k`
the map `k ⟶ κ(z)` is the map `k ⟶ κ(i z)` followed by the residue field map of `i`. -/
theorem fieldToResidue_comp {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (z : Z) :
    fieldToResidue (i ≫ f) z = fieldToResidue f (i.base z) ≫ i.residueFieldMap z := by
  rw [fieldToResidue_eq_residueFieldMap, fieldToResidue_eq_residueFieldMap,
    Scheme.residueFieldMap_comp, Category.assoc]
  rfl

end AlgebraicGeometry

namespace Stacks.Curves

/-! ### The residue field at a closed point as an extension of the residue field of the base -/

/-- **The residue field at a closed point of a scheme locally of finite type over a field is a
finite extension of that field.**  It is a field of finite type over `k`, so Zariski's lemma
applies. -/
theorem module_finite_fieldToResidue {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Algebra.FiniteType k (X.residueField x) :=
    Stacks.EtaleCohomology.finiteType_fieldToResidue f x hx
  exact finite_of_finite_type_of_isJacobsonRing k (X.residueField x)

/-- **The ground field, the residue field of the image point and the residue field at the point
form a tower.**  This is `AlgebraicGeometry.fieldToResidue_eq_residueFieldMap` read as a scalar
tower. -/
theorem isScalarTower_residueField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
    letI : Algebra k ((Spec (.of k)).residueField (f.base x)) :=
      ((specFieldResidueIso k (f.base x)).inv).hom.toAlgebra
    letI : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower k ((Spec (.of k)).residueField (f.base x)) (X.residueField x) := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  let : Algebra k ((Spec (.of k)).residueField (f.base x)) :=
    ((specFieldResidueIso k (f.base x)).inv).hom.toAlgebra
  let : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (fieldToResidue f x).hom = _
  rw [fieldToResidue_eq_residueFieldMap]
  rfl

end Stacks.Curves

end
