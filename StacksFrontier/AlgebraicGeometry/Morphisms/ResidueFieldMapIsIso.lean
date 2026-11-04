module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue fields along an isomorphism

An open immersion induces an isomorphism on residue fields, which Mathlib records as an
instance. An isomorphism of schemes is in particular an open immersion, so it too induces an
isomorphism on the residue field at every point; this file names that specialization, which is
not itself an instance because `IsIso` is not an `IsOpenImmersion`-shaped hypothesis that
instance search would chain through at the point.

## Main results

* `AlgebraicGeometry.residueFieldMap_isIso_of_isIso`: an isomorphism of schemes induces an
  isomorphism on the residue field at every point of the source.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes induces an isomorphism on every residue field. -/
public theorem residueFieldMap_isIso_of_isIso {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIso g] (x : A) : IsIso (g.residueFieldMap x) := by
  let : IsOpenImmersion g := inferInstance
  exact inferInstance

end AlgebraicGeometry

end
