module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.LocallyClosed
public import StacksCore.Tactic.StacksAttribute

/-! # Staged copy of Stacks Tag 0F2L: the reduced induced scheme structure on a locally closed
subset

The construction needs nothing beyond Mathlib's quasi-coherent ideal sheaves and the
`coborder` API: the open complement of the boundary, the subset as a closed set inside it, and
the vanishing ideal of that closed set. -/

@[expose] public section

open AlgebraicGeometry TopologicalSpace CategoryTheory


namespace Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

/-- The open complement of the boundary of a locally closed subset. -/
abbrev reducedInducedOpen {X : Scheme.{u}} (T : Set X) (hT : IsLocallyClosed T) : X.Opens :=
  ⟨coborder T, hT.isOpen_coborder⟩

/-- A locally closed subset as a closed set in the complement of its boundary. -/
abbrev reducedInducedClosed {X : Scheme.{u}} (T : Set X) (hT : IsLocallyClosed T) :
    Closeds (reducedInducedOpen T hT).toScheme :=
  ⟨Subtype.val ⁻¹' T, isClosed_preimage_val_coborder⟩

/-- The defining ideal sheaf of the reduced induced scheme structure on a locally
closed subset. -/
@[stacks 0F2L "reduced_induced_scheme_structure_on_a_locally_closed_subset"]
noncomputable def reducedInducedIdealSheaf {X : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) : (reducedInducedOpen T hT).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (reducedInducedClosed T hT)

/-- The reduced scheme induced on a locally closed subset. -/
noncomputable abbrev reducedInducedScheme {X : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) : Scheme.{u} :=
  (reducedInducedIdealSheaf T hT).subscheme

/-- The canonical immersion of the reduced induced scheme into the ambient scheme. -/
noncomputable abbrev reducedInducedInclusion {X : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) : reducedInducedScheme T hT ⟶ X :=
  (reducedInducedIdealSheaf T hT).subschemeι ≫ (reducedInducedOpen T hT).ι

end Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed


end
