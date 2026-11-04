module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Naturality of the global sections of an open subscheme

Let `X` be a scheme and `U ≤ V` two opens of `X`. The sections of `X` over `V` are the global
sections of the open subscheme `V`, by `AlgebraicGeometry.Scheme.Opens.topIso`, and under this
identification the restriction map `Γ(X, V) ⟶ Γ(X, U)` of the structure sheaf is the map on
global sections induced by the inclusion `AlgebraicGeometry.Scheme.homOfLE` of open
subschemes.

## Main results

* `AlgebraicGeometry.opens_topIso_naturality`

## Implementation notes

The inclusion of open subschemes is the restriction of the identity of `X` to `V` and `U`, so
the statement is Mathlib's `AlgebraicGeometry.Scheme.Hom.resLE_app_top` at the identity, the
two containment proofs agreeing because the opens of `X` form a partial order.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The identification of the sections on an open with the global sections of the corresponding
open subscheme is natural in the open. -/
lemma opens_topIso_naturality {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE h).appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE h).op := by
  have := Scheme.Hom.resLE_app_top (𝟙 X) (show U ≤ (𝟙 X) ⁻¹ᵁ V from h)
  rw [Scheme.Hom.resLE_id h] at this
  rw [Scheme.Hom.appTop, this]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry

end
