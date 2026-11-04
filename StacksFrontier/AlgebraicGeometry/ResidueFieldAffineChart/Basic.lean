module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Closed points over a field

A point of a scheme of finite type over a field whose residue field is a finite extension is a
closed point.  Mathlib has the converse in several forms and has the criterion
`AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType`; the step that is missing is the
computation of the global sections of `AlgebraicGeometry.Scheme.fromSpecResidueField`, which is
what turns a finiteness hypothesis on the residue field into that criterion.

## Main results

* `AlgebraicGeometry.Scheme.fromSpecResidueField_appTop`: the canonical morphism
  `Spec κ(x) ⟶ X` is, on global sections, evaluation at `x`.
* `AlgebraicGeometry.isClosed_singleton_of_module_finite_residueField`: **a point with finite
  residue field extension over the base field is closed**, for a morphism locally of finite type
  to the spectrum of a field.

## Implementation notes

The `k`-algebra structure on `X.residueField x` used in the closedness criterion is the one
coming from the structure morphism through global sections,
`(Scheme.ΓSpecIso _).inv ≫ f.appTop ≫ X.Γevaluation x`; the criterion is stated with that
structure supplied by `letI` rather than by an instance, since a scheme can be a `k`-scheme in
more than one way.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- **The canonical morphism `Spec κ(x) ⟶ X` is evaluation at `x` on global sections.** -/
theorem Scheme.fromSpecResidueField_appTop (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).appTop =
      X.Γevaluation x ≫ (Scheme.ΓSpecIso (X.residueField x)).inv := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.Γevaluation]
  simp [← Scheme.ΓSpecIso_inv_naturality, Scheme.evaluation]

/-- **A point whose residue field is a finite extension of the base field is closed.**
If `f : X ⟶ Spec k` is locally of finite type and `κ(x)` is a finite `k`-module, then `{x}` is
closed in `X`.

This is the converse of the familiar direction and is what lets a closed point be produced from
commutative algebra: the degree bound of a residue extension is an algebraic statement, while
being a closed point is a topological one. -/
theorem isClosed_singleton_of_module_finite_residueField {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X)
    (h : letI := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
          X.Γevaluation x).hom.toAlgebra
        Module.Finite k (X.residueField x)) :
    IsClosed ({x} : Set X) := by
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
    X.Γevaluation x).hom.toAlgebra
  have : Module.Finite k (X.residueField x) := h
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [isClosed_singleton_iff_locallyOfFiniteType]
  have hcomp : ((X.fromSpecResidueField x ≫ f).appTop).hom =
      (Scheme.ΓSpecIso (X.residueField x)).inv.hom.comp
        (f.appTop ≫ X.Γevaluation x).hom := by
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecResidueField_appTop, ← Category.assoc,
      CommRingCat.hom_comp]
  have hft : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType), hcomp,
      RingHom.finiteType_respectsIso.cancel_right_isIso
        (f.appTop ≫ X.Γevaluation x) (Scheme.ΓSpecIso (X.residueField x)).inv,
      ← RingHom.finiteType_respectsIso.cancel_left_isIso
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv (f.appTop ≫ X.Γevaluation x)]
    exact inferInstanceAs (Algebra.FiniteType k (X.residueField x))
  exact locallyOfFiniteType_of_comp (X.fromSpecResidueField x) f

end AlgebraicGeometry

end
