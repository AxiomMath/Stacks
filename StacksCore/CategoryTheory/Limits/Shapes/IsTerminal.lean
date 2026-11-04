module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Initial objects: mirror lemmas

A monomorphism into an initial object is an isomorphism (it is split epi by
`IsInitial.isSplitEpi_to`), so its source is initial. Mathlib has `IsInitial.isIso_to` only under
`HasStrictInitialObjects`; these two hold in any category.
-/

@[expose] public section

namespace CategoryTheory.Limits.IsInitial

variable {C : Type*} [Category* C]

/-- A monomorphism into an initial object is an isomorphism: it is split epi
(`IsInitial.isSplitEpi_to`). -/
lemma isIso_of_mono {Y Z : C} (hZ : IsInitial Z) (g : Y ⟶ Z) [Mono g] : IsIso g :=
  have := hZ.isSplitEpi_to g
  isIso_of_mono_of_isSplitEpi g

/-- The source of a monomorphism into an initial object is initial. -/
noncomputable def ofMono {Y Z : C} (hZ : IsInitial Z) (g : Y ⟶ Z) [Mono g] : IsInitial Y :=
  have := hZ.isIso_of_mono g
  hZ.ofIso (asIso g).symm

end CategoryTheory.Limits.IsInitial
