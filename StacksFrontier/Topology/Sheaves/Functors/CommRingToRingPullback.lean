module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Inverse image of a sheaf of rings and forgetting commutativity

For a continuous map `i : Z ⟶ W` of topological spaces and a sheaf of commutative rings `S` on
`W`, the inverse image `i⁻¹S` may be formed in sheaves of commutative rings or, after forgetting
commutativity, in sheaves of rings. The forgetful functor `CommRingCat ⥤ RingCat` preserves
filtered colimits and sheafification, and the comma categories computing the presheaf-level
inverse image along `(Opens.map i).op` are filtered, so the general comparison
`CategoryTheory.Functor.sheafPullbackSheafComposeIso` applies and the two agree.

## Main definitions

* `TopCat.Sheaf.pullbackForget₂Iso` is the resulting isomorphism.

## Main results

* `AlgebraicGeometry.preservesColimitsOfShape_costructuredArrow_opensMap_forget₂`,
  `AlgebraicGeometry.preservesSheafification_opensGrothendieckTopology_forget₂` and
  `AlgebraicGeometry.hasSheafCompose_opensGrothendieckTopology_forget₂` record the three
  hypotheses on `CommRingCat ⥤ RingCat` that the general comparison consumes.

## Implementation notes

The three instances are recorded here, in a module with few imports, and at high priority:
each is already a consequence of Mathlib's generic instances, but reconstructing that
consequence costs more than the default instance-search budget allows in a module with many
imports.

## References

* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {Z W : TopCat.{u}} (i : Z ⟶ W)

/-- The forgetful functor from commutative rings to rings preserves the colimits computing the
presheaf-level inverse image along a continuous map, since those are filtered. -/
instance (priority := 10000) preservesColimitsOfShape_costructuredArrow_opensMap_forget₂
    (V : (Opens Z)ᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow (Opens.map i).op V)
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  PreservesFilteredColimitsOfSize.preserves_filtered_colimits _

/-- The forgetful functor from commutative rings to rings preserves sheafification for the
open-cover topology on a topological space. -/
instance (priority := 10000) preservesSheafification_opensGrothendieckTopology_forget₂ :
    (Opens.grothendieckTopology Z).PreservesSheafification
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstance

/-- Composing a sheaf of commutative rings with the forgetful functor to rings gives a sheaf of
rings. -/
instance (priority := 10000) hasSheafCompose_opensGrothendieckTopology_forget₂ :
    (Opens.grothendieckTopology Z).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstance

end AlgebraicGeometry

namespace TopCat.Sheaf

open AlgebraicGeometry

universe u

variable {Z W : TopCat.{u}} (i : Z ⟶ W) (S : TopCat.Sheaf CommRingCat.{u} W)

/-- The inverse image of a sheaf of commutative rings, formed in sheaves of rings after
forgetting commutativity, agrees with the inverse image formed in sheaves of commutative
rings. -/
noncomputable def pullbackForget₂Iso :
    (TopCat.Sheaf.pullback RingCat.{u} i).obj
        ((sheafCompose (Opens.grothendieckTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          S) ≅
      (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj S) :=
  Functor.sheafPullbackSheafComposeIso (Opens.map i) CommRingCat.{u}
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)
    (forget₂ CommRingCat.{u} RingCat.{u}) S

/-- The forward map of `pullbackForget₂Iso` is the canonical comparison morphism
`CategoryTheory.Functor.sheafPullbackSheafComposeHom`. -/
lemma pullbackForget₂Iso_hom :
    (pullbackForget₂Iso i S).hom =
      Functor.sheafPullbackSheafComposeHom (Opens.map i) CommRingCat.{u}
        (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)
        (forget₂ CommRingCat.{u} RingCat.{u}) S :=
  rfl

end TopCat.Sheaf
