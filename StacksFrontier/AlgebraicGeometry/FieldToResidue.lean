module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The structural maps from the ground field to a stalk and to a residue field

A scheme `X` over a field `k` has, at each point `x`, a structural map from `k` to the local ring
`𝒪_{X,x}` — the germ at `x` of the structure morphism — and, composing with the residue map, one
from `k` to the residue field `κ(x)`. These present `𝒪_{X,x}` and `κ(x)` as `k`-algebras.

## Main definitions

* `AlgebraicGeometry.fieldToStalk` is the map from the ground field to the local ring at a point.
* `AlgebraicGeometry.fieldToResidue` is the map from the ground field to the residue field.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The map from the ground field to the local ring at a point of a scheme over that field. -/
public def fieldToStalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    CommRingCat.of k ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial

/-- The map from the ground field to the residue field at a point of a scheme over it. -/
public def fieldToResidue {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : CommRingCat.of k ⟶ X.residueField x :=
  fieldToStalk f x ≫ X.residue x

end AlgebraicGeometry

end
