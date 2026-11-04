module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Étale morphisms induce isomorphisms on separably closed residue fields

An étale morphism of schemes induces a separable algebraic residue field extension at every
point. So at a point whose image has *separably closed* residue field the extension is trivial:
the residue field map is an isomorphism.

This is the step of [Stacks Project, Tag 0DT9] which reads, in the source text, "As `U' → U` is
étale, we conclude the morphism `U'_{p'} → U_p` induces isomorphisms on residue field
extensions" — the residue fields of the points of `U_p` being separably closed because they are
algebraic over the separably closed residue field of the closed point of a strictly henselian
local ring.

## Main results

* `AlgebraicGeometry.Scheme.Hom.bijective_residueFieldMap_of_etale`: **the residue field map of
  an étale morphism at a point whose image has separably closed residue field is bijective.**
* `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_etale`: the same as an isomorphism of
  commutative rings.

## Implementation notes

Separability of the residue field extension of an étale morphism is already available in
Mathlib, as an anonymous instance for a formally unramified morphism locally of finite type
(in `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`); it is stated for the algebra
structure `(f.residueFieldMap x).hom.toAlgebra`, which is therefore the one installed here.
What is added is the passage to a separably closed base, which is
`IsSepClosed.algebraMap_bijective` — note this needs no finiteness, only separability.

## References

* [Stacks Project, Tag 02GH](https://stacks.math.columbia.edu/tag/02GH)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X)

/-- **The residue field map of an étale morphism at a point whose image has separably closed
residue field is bijective.**

An étale morphism induces a separable residue field extension, and a separable extension of a
separably closed field is an equality. -/
theorem bijective_residueFieldMap_of_etale [IsSepClosed (Y.residueField (f.base x))] :
    Function.Bijective (f.residueFieldMap x).hom := by
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact IsSepClosed.algebraMap_bijective (Y.residueField (f.base x)) (X.residueField x)

/-- The residue field map of an étale morphism at a point whose image has separably closed
residue field is an isomorphism of commutative rings. -/
theorem isIso_residueFieldMap_of_etale [IsSepClosed (Y.residueField (f.base x))] :
    IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_residueFieldMap_of_etale f x)

end AlgebraicGeometry.Scheme.Hom

end

end
