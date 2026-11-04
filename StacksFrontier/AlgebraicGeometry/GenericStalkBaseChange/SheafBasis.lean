module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Recognising an isomorphism of sheaves of modules on a basis

A morphism of sheaves of modules on a space which is an isomorphism on the sections over every
member of a basis of the topology is an isomorphism. This is the step that converts a computation
of the sections over the affine opens into a statement about sheaves whose sections over an
arbitrary open set are inaccessible — for instance a sheafification.

## Main results

* `Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis`: the criterion.

## Implementation notes

Both halves are already in Mathlib and only need to be put together.
`CategoryTheory.TopCat.Sheaf.isIso_iff_isIso_basis` is the criterion for sheaves valued in an
arbitrary category, and `CategoryTheory.SheafOfModules.toSheaf` reflects isomorphisms, so it
suffices to know that the underlying morphism of sheaves of abelian groups is an isomorphism on
the basis. On an open set the component of that morphism is the image of the component of the
original one under `forget₂ (ModuleCat _) AddCommGrpCat`, which preserves isomorphisms.

The statement is in terms of `φ.val.app`, which is the form a computation of sections produces,
rather than in terms of the morphism of sheaves of abelian groups.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.GenericStalkBaseChange

variable {Y : TopCat.{u}} {ι : Type*} {B : ι → Opens Y}
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} {M N : SheafOfModules.{v} R}

/-- A morphism of sheaves of modules which is an isomorphism on the sections over every member of
a basis of the topology is an isomorphism. -/
theorem isIso_of_isIso_val_app_basis (hB : Opens.IsBasis (Set.range B)) (φ : M ⟶ N)
    (h : ∀ i, IsIso (φ.val.app (op (B i)))) : IsIso φ := by
  have : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis hB (fun i ↦ ?_)
    have := h i
    exact inferInstanceAs
      (IsIso ((forget₂ (ModuleCat (R.obj.obj (op (B i)))) AddCommGrpCat.{v}).map
        (φ.val.app (op (B i)))))
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf R)

end Stacks.AlgebraicGeometry.GenericStalkBaseChange

end

