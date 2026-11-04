module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FunctionsOnIntersection

/-!
# Restricting functions to a subset of a scheme

The ring of functions on an arbitrary subset `E` of a scheme `X` is the ring of global sections
of the inverse image of the structure sheaf along the inclusion of `E` with its subspace
topology. This file records the canonical restriction maps to that ring: from the functions on
an open neighbourhood of `E`, and in particular from the global functions on `X`.

These maps are the ones that appear in the comparison of the functions on an intersection of
quasi-compact opens with the filtered colimit of the functions on the members of the family: the
canonical map out of a member of such a family is precisely the restriction from that member,
viewed as an open neighbourhood of the intersection.

## Main definitions

* `AlgebraicGeometry.Scheme.restrictOpenToSubset` is the restriction of the functions on an open
  neighbourhood of a subset to the functions on that subset.
* `AlgebraicGeometry.Scheme.restrictToSubset` is the restriction of the global functions on a
  scheme to the functions on a subset.

## Main results

* `AlgebraicGeometry.Scheme.stageToSubset_eq_restrictOpenToSubset` identifies the canonical map
  out of a member of a decreasing family of opens with the restriction from that member.
* `AlgebraicGeometry.Scheme.map_comp_restrictOpenToSubset` says that the restrictions from the
  open neighbourhoods of a subset are compatible with the restriction maps of the structure
  sheaf.

## Implementation notes

The subset carries the subspace topology, and the inverse image of the structure sheaf along its
inclusion is formed in sheaves of commutative rings; the restriction map is the component of the
unit of the inverse-image adjunction followed by the restriction to the whole subset. Because the
order relation on the opens of a subset is a proposition, the two maps compared in
`AlgebraicGeometry.Scheme.stageToSubset_eq_restrictOpenToSubset` are definitionally equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The canonical map from the functions on an open neighbourhood `U` of a subset `E` of a scheme
`X` to the functions on `E`, that is to the global sections of the inverse image of the structure
sheaf along the inclusion of `E` with its subspace topology. -/
noncomputable def Scheme.restrictOpenToSubset (X : Scheme.{u}) (E : Set X) (U : X.Opens)
    (hE : E ⊆ U) :
    Γ(X, U) ⟶ X.sectionsRingOnSubset E :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
        X.toSheafedSpace.sheaf).hom.app (op U) ≫
    ((TopCat.Sheaf.pullback CommRingCat.{u} (Stacks.subsetInclusion (TopCat.of X) E)).obj
      X.toSheafedSpace.sheaf).obj.map (homOfLE (by
        intro x _
        exact hE x.2)).op

/-- The canonical map out of a member of a decreasing family of opens containing a subset is the
restriction from that member, regarded as an open neighbourhood of the subset. -/
theorem Scheme.stageToSubset_eq_restrictOpenToSubset (X : Scheme.{u}) {I : Type u}
    (U : I → X.Opens) (E : Set X) (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U) :
    X.stageToSubset U E hE i = X.restrictOpenToSubset E (U i.val) (hE i.val) :=
  rfl

/-- Restricting the functions on an open neighbourhood of a subset to a smaller open
neighbourhood and then to the subset is restricting to the subset directly. -/
theorem Scheme.map_comp_restrictOpenToSubset {X : Scheme.{u}} (E : Set X) {U W : X.Opens}
    (hUW : U ≤ W) (hEU : E ⊆ U) :
    X.presheaf.map (homOfLE hUW).op ≫ X.restrictOpenToSubset E U hEU =
      X.restrictOpenToSubset E W (hEU.trans hUW) := by
  let G := TopCat.Sheaf.pullback CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)
  let P := (G.obj X.toSheafedSpace.sheaf).obj
  let η := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (Stacks.subsetInclusion (TopCat.of X) E)
  let VU : TopologicalSpace.Opens E :=
    (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj U
  let VW : TopologicalSpace.Opens E :=
    (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj W
  let i : op W ⟶ op U := (homOfLE hUW).op
  let iE : op VW ⟶ op VU :=
    ((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).map i.unop).op
  let aU : op VU ⟶ op ⊤ := (homOfLE (by
    intro x _
    exact hEU x.2)).op
  let aW : op VW ⟶ op ⊤ := (homOfLE (by
    intro x _
    exact (hEU.trans hUW) x.2)).op
  have hnat := (η.unit.app X.toSheafedSpace.sheaf).hom.naturality i
  change X.toSheafedSpace.sheaf.obj.map i ≫
      (η.unit.app X.toSheafedSpace.sheaf).hom.app (op U) =
    (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫
      ((G ⋙ TopCat.Sheaf.pushforward CommRingCat
        (Stacks.subsetInclusion (TopCat.of X) E)).obj
        X.toSheafedSpace.sheaf).obj.map i at hnat
  dsimp [Scheme.restrictOpenToSubset]
  show X.toSheafedSpace.sheaf.obj.map i ≫
      (η.unit.app X.toSheafedSpace.sheaf).hom.app (op U) ≫
        (G.obj X.toSheafedSpace.sheaf).obj.map aU =
    (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫
      (G.obj X.toSheafedSpace.sheaf).obj.map aW
  calc
    (X.toSheafedSpace.sheaf.obj.map i ≫
        (η.unit.app X.toSheafedSpace.sheaf).hom.app (op U)) ≫ P.map aU =
      ((η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫ P.map iE) ≫ P.map aU := by
        rw [hnat]
        rfl
    _ = (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫ P.map aW := by
      calc
        _ = (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫
              (P.map iE ≫ P.map aU) := Category.assoc _ _ _
        _ = (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫ P.map (iE ≫ aU) :=
          congrArg ((η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫ ·) (P.map_comp iE aU).symm
        _ = (η.unit.app X.toSheafedSpace.sheaf).hom.app (op W) ≫ P.map aW := rfl

/-- The restriction of the global functions on a scheme to the functions on a subset. -/
noncomputable def Scheme.restrictToSubset (X : Scheme.{u}) (E : Set X) :
    Γ(X, ⊤) ⟶ X.sectionsRingOnSubset E :=
  X.restrictOpenToSubset E ⊤ (Set.subset_univ E)

end AlgebraicGeometry

end
