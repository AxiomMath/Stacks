module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomRestrictionInSituation0D67

/-!
# Restriction of a morphism of modules to a smaller open, across the open-subspace model

Let `O` be a sheaf of rings on a topological space `Z`.  There are two models of the modules on
an open `W`: the *slice* model, sheaves of modules over `O.over W` on the site of the opens
contained in `W`, and the *open-subspace* model, sheaves of modules on the space `W` itself.  The
two are identified by the equivalence `Stacks.DerivedGlueing.sliceToSubspace`.

Passing to a smaller open `T ≤ W` is `CategoryTheory.SheafOfModules.overMap` in the slice model,
and "extend by zero, then restrict" —
`ExtensionByZeroModules.jShriek W O ⋙ ExtensionByZeroModules.jStar T O` — in the open-subspace
model.  This file records that the identification intertwines the two, as a natural isomorphism
of functors on the slice category over `W`
(`Stacks.DerivedGlueing.overMapSliceToSubspaceIso`), and spells out what that gives on
morphisms (`Stacks.DerivedGlueing.sliceToSubspace_map_overMap_map`).

**Why the naturality is the point.**  A gluing of locally given morphisms has, over each member
of a covering, a morphism of the restrictions which does *not* come from a morphism of global
modules — it is precisely the unknown being glued.  What the gluing needs is that restricting
such a morphism to a smaller open commutes with the identification of the two models, and that is
naturality of the crossing at an **arbitrary** morphism of the slice category.  Whiskering a
crossing with `CategoryTheory.SheafOfModules.overFunctor`, which is what an identification stated
only on restrictions of global modules provides, carries none of that content.

## Main definitions

* `Stacks.DerivedGlueing.overMapSliceToSubspaceIso`: **the nested-open crossing** — reading a
  module on the slice site over `W` in the open-subspace model and restricting it to the subspace
  `T` is restricting it to the slice site over `T` and reading that in the open-subspace model.

## Main results

* `Stacks.DerivedGlueing.sliceToSubspace_map_overMap_map`: **the nested-open crossing coherence**
  — the open-subspace model of the restriction to `T` of a morphism given over `W` is the
  restriction between the two open subspaces of its open-subspace model over `W`, conjugated by
  the crossing.

## Implementation notes

**Both statements are made at an arbitrary sheaf of rings on an arbitrary topological space.**
That is what makes them provable without weakening anything.  The same compatibility for the
structure sheaf of a scheme is Mathlib's
`AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv`, which is proved under a
transparency-relaxing compiler option; there the sheaf of rings is
`AlgebraicGeometry.Scheme.ringCatSheaf`, which unfolds to the sheaf that
`CategoryTheory.SheafOfModules` wants only at default transparency, so a goal about modules over
it is not type-correct at the transparency a rewrite motive is built at.  At an arbitrary sheaf of
rings there is nothing to unfold, that obstruction does not arise, and the crossing is assembled
from two factors the development already has —
`Stacks.DerivedGlueing.sliceRestrictOverIso` and
`Stacks.DerivedGlueing.slice_comp_jShriek_jStar_eq`.

**The coherence is stated at variable objects of the slice category, not at restrictions of
global modules.**  Written at `M.over W` and `N.over W` it does not elaborate: matching the
target of the crossing against the restriction of `M` to the subspace `T` forces the three-fold
composite `overFunctor W ⋙ overMap ⋙ sliceToSubspace T` to be compared with
`ExtensionByZeroModules.jStar T O` by `whnf`, and that comparison exhausts the heartbeat budget —
the cost recorded in the docstring of
`Stacks.DerivedGlueing.overFunctor_comp_overMap_comp_sliceToSubspace`, which exists for exactly
this reason.  At variable objects there is no such comparison to make, the statement is strictly
more general, and a consumer instantiates it where the identification it needs is the two-fold
one.

The restriction between the two open subspaces is written out as
`ExtensionByZeroModules.jShriek W O ⋙ ExtensionByZeroModules.jStar T O` rather than given a name:
the named form exists already, as `Stacks.openModuleRestriction`, but only at a `RingedSpace`, and
a second name for the same composite at an arbitrary sheaf of rings would duplicate it.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open ExtensionByZeroModules

universe u

namespace Stacks.DerivedGlueing

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **The nested-open crossing.**  For `T ≤ W`, reading a module given on the slice site over `W`
in the open-subspace model and then restricting it to the subspace `T` is the same as restricting
it to the slice site over `T` and reading that in the open-subspace model of `T`.

This is `Stacks.DerivedGlueing.sliceRestrictOverIso` with its source rewritten by
`Stacks.DerivedGlueing.slice_comp_jShriek_jStar_eq`, so that the restriction between the two
subspaces appears as the composite "extend by zero, then restrict" rather than as a four-fold
composite back through the slice model. -/
def overMapSliceToSubspaceIso {T W : Opens Z} (hTW : T ≤ W) :
    sliceToSubspace O W ⋙ (jShriek W O ⋙ jStar T O) ≅
      SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T :=
  eqToIso (slice_comp_jShriek_jStar_eq O hTW).symm ≪≫ sliceRestrictOverIso O hTW

/-- **The nested-open crossing coherence.**  For an arbitrary morphism `φ` of modules on the
slice site over `W`, the open-subspace model of its restriction to the slice site over a smaller
open `T` is the restriction between the two open subspaces of its own open-subspace model,
conjugated by the crossing isomorphism.

This is naturality of `Stacks.DerivedGlueing.overMapSliceToSubspaceIso` at `φ`.  The morphism is
arbitrary — in particular it is not assumed to be the restriction of a morphism of modules on
`Z` — which is the content a gluing of locally given morphisms consumes. -/
theorem sliceToSubspace_map_overMap_map {T W : Opens Z} (hTW : T ≤ W)
    {A B : SheafOfModules.{u} (O.over W)} (φ : A ⟶ B) :
    (sliceToSubspace O T).map ((SheafOfModules.overMap.{u} O hTW.hom).map φ) =
      (overMapSliceToSubspaceIso O hTW).inv.app A ≫
        (jShriek W O ⋙ jStar T O).map ((sliceToSubspace O W).map φ) ≫
        (overMapSliceToSubspaceIso O hTW).hom.app B :=
  (Iso.inv_hom_id_app_assoc (overMapSliceToSubspaceIso O hTW) A
        ((SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T).map φ)).symm.trans
    (congrArg
      (fun t => (overMapSliceToSubspaceIso O hTW).inv.app A ≫ t)
      ((overMapSliceToSubspaceIso O hTW).hom.naturality φ).symm)

end Stacks.DerivedGlueing

end
