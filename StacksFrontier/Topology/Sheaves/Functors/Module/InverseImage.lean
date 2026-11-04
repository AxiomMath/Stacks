module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf

/-!
# The inverse image of a sheaf of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces, let `O` be a sheaf of rings
on `Y` and let `G` be a sheaf of `O`-modules.  Following the Stacks Project, the inverse
image `f⁻¹` is the sheafification of the presheaf-level pullback `f_p`; the latter carries
a `f_p O`-module structure on `f_p G` by Tag 008T.  Sheafifying that module structure
(Tag 0089, in the form of `PresheafOfModules.sheafify`) endows `f⁻¹G` with the structure
of a sheaf of `f⁻¹O`-modules, compatibly with the presheaf-level action.

## Main results

* `InverseImageModules.exists_moduleStructure_inverseImage`: Stacks Tag 008X.  There is a
  sheaf of `f⁻¹O`-modules whose underlying sheaf of abelian groups is `f⁻¹G`, and whose
  scalar multiplication extends the presheaf-level one along the sheafification map.
* `InverseImageModules.inverseImageRingIsoPullback` and
  `InverseImageModules.inverseImageAbIsoPullback` identify the sheafification-of-`f_p`
  description of `f⁻¹` used here with Mathlib's `TopCat.Sheaf.pullback`.

## Implementation notes

**Universes.** Everything here is stated at a single universe `u` carrying the space, the
rings and the module sections together.  That single universe is forced, not chosen:
`TopCat.Presheaf.pullback` requires the hom universe of the target category to equal the
universe of the space, so `pullbackRing` already ties `RingCat.{u}` to `TopCat.{u}`, and
`PresheafOfModules.ModuleColimit` (used in
`StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf`) ties the module universe to
the ring universe.  The `RingCat`, `AddCommGrpCat` and `SheafOfModules` arguments must be
written `.{u}` explicitly: left implicit they default to `0` and silently collapse every
universe in the statement.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Stacks.PresheafOfModules.Pullback

universe u

namespace InverseImageModules

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Sheaf RingCat.{u} Y)

/-- The inverse image sheaf of rings `f⁻¹O`, defined as in the Stacks Project as the
sheafification of the pullback presheaf of rings `f_p O` of Tag 008T. -/
noncomputable def inverseImageRing : TopCat.Sheaf RingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{u}).obj (pullbackRing f O.obj)

/-- `inverseImageRing` agrees with Mathlib's pullback of sheaves
`TopCat.Sheaf.pullback`, which is defined as the left adjoint of the pushforward. -/
noncomputable def inverseImageRingIsoPullback :
    inverseImageRing f O ≅ (TopCat.Sheaf.pullback RingCat.{u} f).obj O :=
  ((TopCat.Sheaf.pullbackIso RingCat.{u} f).app O).symm

/-- The sheafification map `f_p O ⟶ f⁻¹O` of presheaves of rings. -/
noncomputable def toInverseImageRing : pullbackRing f O.obj ⟶ (inverseImageRing f O).obj :=
  toSheafify (Opens.grothendieckTopology X) (pullbackRing f O.obj)

/-- The sheafification map `f_p O ⟶ f⁻¹O` is locally injective: two sections of `f_p O` with the
same image agree locally on a covering. -/
instance isLocallyInjective_toInverseImageRing :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (toInverseImageRing f O) :=
  inferInstanceAs (Presheaf.IsLocallyInjective _
    (toSheafify (Opens.grothendieckTopology X) (pullbackRing f O.obj)))

/-- The sheafification map `f_p O ⟶ f⁻¹O` is locally surjective: every section of `f⁻¹O` comes,
locally on a covering, from a section of `f_p O`. -/
instance isLocallySurjective_toInverseImageRing :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (toInverseImageRing f O) :=
  inferInstanceAs (Presheaf.IsLocallySurjective _
    (toSheafify (Opens.grothendieckTopology X) (pullbackRing f O.obj)))

variable (G : SheafOfModules.{u} O)

/-- The pullback presheaf of `f_p O`-modules `f_p G` supplied by Tag 008T; its underlying
presheaf of abelian groups is the pullback presheaf `f_p` of the one underlying `G`. -/
noncomputable def pullbackPresheafOfModules : PresheafOfModules.{u} (pullbackRing f O.obj) :=
  (pullbackModuleFunctor f O.obj).obj G.val

/-- The inverse image sheaf of abelian groups `f⁻¹G`, defined as in the Stacks Project as
the sheafification of the pullback presheaf `f_p G`. -/
noncomputable def inverseImageAb : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (pullbackPresheafOfModules f O G).presheaf

/-- `inverseImageAb` agrees with Mathlib's pullback of sheaves of abelian groups
`TopCat.Sheaf.pullback` applied to the sheaf of abelian groups underlying `G`. -/
noncomputable def inverseImageAbIsoPullback :
    inverseImageAb f O G ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj ⟨G.val.presheaf, G.isSheaf⟩ :=
  ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).app ⟨G.val.presheaf, G.isSheaf⟩).symm

/-- The sheafification map `f_p G ⟶ f⁻¹G` of presheaves of abelian groups. -/
noncomputable def toInverseImageAb :
    (pullbackPresheafOfModules f O G).presheaf ⟶ (inverseImageAb f O G).obj :=
  toSheafify (Opens.grothendieckTopology X) (pullbackPresheafOfModules f O G).presheaf

/-- The sheafification map `f_p G ⟶ f⁻¹G` of presheaves of abelian groups is locally injective. -/
instance isLocallyInjective_toInverseImageAb :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (toInverseImageAb f O G) :=
  inferInstanceAs (Presheaf.IsLocallyInjective _
    (toSheafify (Opens.grothendieckTopology X) (pullbackPresheafOfModules f O G).presheaf))

/-- The sheafification map `f_p G ⟶ f⁻¹G` of presheaves of abelian groups is locally surjective;
together with local injectivity this is what lets the module structure be sheafified. -/
instance isLocallySurjective_toInverseImageAb :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (toInverseImageAb f O G) :=
  inferInstanceAs (Presheaf.IsLocallySurjective _
    (toSheafify (Opens.grothendieckTopology X) (pullbackPresheafOfModules f O G).presheaf))

/-- The inverse image `f⁻¹G` as a sheaf of `f⁻¹O`-modules: sheafify the `f_p O`-module
structure on `f_p G` of Tag 008T along the sheafification maps, using Tag 0089 in the form
of `PresheafOfModules.sheafify`. -/
noncomputable def inverseImageSheafOfModules : SheafOfModules.{u} (inverseImageRing f O) :=
  PresheafOfModules.sheafify (toInverseImageRing f O) (toInverseImageAb f O G)

/-- **Stacks Tag 008X.**

Let `f : X ⟶ Y` be a continuous map, `O` a sheaf of rings on `Y` and `G` a sheaf of
`O`-modules.  There is a scalar multiplication turning `f⁻¹G` into a sheaf of
`f⁻¹O`-modules, and it is natural in the sense that it extends the presheaf-level scalar
multiplication `f_p O × f_p G → f_p G` of Tag 008T along the sheafification maps.

Concretely: there is a sheaf of `f⁻¹O`-modules `M` whose underlying presheaf of abelian
groups is literally `f⁻¹G`, together with a morphism `ι` of presheaves of `f_p O`-modules
from `f_p G` to `M` restricted along `f_p O ⟶ f⁻¹O`, whose underlying morphism of
presheaves of abelian groups is the sheafification map `f_p G ⟶ f⁻¹G`. -/
@[stacks 008X]
theorem exists_moduleStructure_inverseImage :
    ∃ (M : SheafOfModules.{u} (inverseImageRing f O))
      (h : M.val.presheaf = (inverseImageAb f O G).obj)
      (ι : pullbackPresheafOfModules f O G ⟶
            (PresheafOfModules.restrictScalars (toInverseImageRing f O)).obj M.val),
      (PresheafOfModules.toPresheaf _).map ι ≫ eqToHom h = toInverseImageAb f O G :=
  ⟨inverseImageSheafOfModules f O G, rfl, PresheafOfModules.toSheafify _ _, rfl⟩

end InverseImageModules
