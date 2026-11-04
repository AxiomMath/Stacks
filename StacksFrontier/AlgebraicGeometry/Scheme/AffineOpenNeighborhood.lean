module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine open neighbourhoods inside a given open

The affine opens of a scheme form a basis of its topology, so every point of an open has an
affine open neighbourhood inside that open.  This is that statement in the packaged form its
consumers want, with the affine open delivered as an element of `X.affineOpens`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An affine open neighbourhood of a point inside a given open neighbourhood. -/
theorem exists_affineOpen_mem_le {X : Scheme.{u}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact ⟨⟨W, hW⟩, hxW, hWle⟩

end AlgebraicGeometry

end
