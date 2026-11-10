module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.PullbackModuleFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of modules along a closed immersion is fully faithful

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is inducing and
whose comorphism `𝒪_X ⟶ i_* 𝒪_Z` of structure sheaves is locally surjective — for instance the
morphism of ringed spaces underlying a closed immersion of schemes. This file feeds that
situation into the ringed-topoi half of Stacks 08M3 through
`StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic`, and reads the conclusion back
as a statement about `RingedSpaceModuleAdjunction.modulePushforward`, hence about
`AlgebraicGeometry.Scheme.Modules.pushforward`.

Only the *full faithfulness* half of Stacks 08M3 comes out this way, and that is the point: full
faithfulness uses nothing about the morphism of topoi beyond its direct image on sheaves of sets
being fully faithful, which holds for an inducing map of spaces, together with local surjectivity
of the structure map. The essential-image half needs the underlying morphism of topoi to be a
*closed immersion of topoi* in the sense of Stacks 08M0 — the essential image of the direct image
on sheaves of sets must be a closed subtopos — and that statement is not available here for a
closed embedding of topological spaces.

## Main definitions

* `Stacks.ToposBridge.fullyFaithfulPushforwardModules`: the full-faithfulness half of Stacks 08M3
  for a morphism of topoi with fully faithful direct image together with a locally surjective map
  of structure sheaves of rings. This is the content of
  `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful` without the
  `AlgebraicGeometry.ClosedRingedImmersion` structure, whose closed-subtopos field that proof does
  not use.
* `Stacks.ToposBridge.fullyFaithfulModulePushforward`: pushforward of sheaves of modules along a
  morphism of ringed spaces with inducing base and locally surjective comorphism is fully
  faithful.
* `Stacks.ToposBridge.fullyFaithfulSchemeModulesPushforward`: pushforward of sheaves of modules
  along a closed immersion of schemes is fully faithful.

## Main results

* `Stacks.ToposBridge.toposStructureRingMap_isLocallySurjective`: the topos-level structure map is
  locally surjective as soon as the comorphism of structure sheaves is.

## Implementation notes

`fullyFaithfulPushforwardModules` takes the full faithfulness of the direct image and the local
surjectivity of the structure map as *explicit* arguments rather than as instances, and is stated
for an abstract site. Both are needed to make it usable at a concrete site: at a concrete site the
universe levels of `CategoryTheory.SheafOfModules` are numerals, while
`CategoryTheory.SheafOfModules.instCategory` carries them inside a `max`, so instance search for
`Category (SheafOfModules R)` does not fire there. Stating the lemma over an abstract site keeps
the levels generic, where it does fire; the lemma is then instantiated.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.PushforwardEssentialImage

universe ww vv uu vv' uu' u

namespace Stacks.ToposBridge

/-! ### The full-faithfulness half of Stacks 08M3 without a closed-subtopos hypothesis -/

section General

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]

/-- **The full-faithfulness half of Stacks 08M3.** Let `f` be a morphism of topoi whose direct
image on sheaves of sets is fully faithful, `O` a sheaf of rings on the source, and
`α : O' ⟶ f_*O` a locally surjective map of sheaves of rings on the target. Then the direct image
`Mod(O) ⥤ Mod(O')` determined by `α` is fully faithful.

The direct image on sheaves of modules is the Stacks 03D1 direct image followed by restriction of
scalars along `α`. The first factor is fully faithful because the direct image of sheaves of sets
is; the second is fully faithful by Stacks 0930, `α` being locally surjective.

No closed-immersion hypothesis enters: this is
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful` with the
closed-subtopos field of `AlgebraicGeometry.ClosedRingedImmersion` dropped, which that proof does
not use either. -/
def fullyFaithfulPushforwardModules
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))
    (O : Sheaf J RingCat.{ww}) {O' : Sheaf K RingCat.{ww}}
    (α : O' ⟶ pushforwardRingSheaf f O) (hf : f.pushforward.FullyFaithful)
    (hα : Sheaf.IsLocallySurjective α) :
    (pushforwardModules f O α).FullyFaithful :=
  letI := hf.full
  letI := hf.faithful
  letI := hα
  (fullyFaithfulPushforwardModuleFunctor f O).comp
    (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective α)

end General

/-! ### Local surjectivity of the structure map of a morphism of ringed spaces -/

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- The structure map of a morphism of ringed spaces, read at the level of sheaves of rings, is
locally surjective as soon as the comorphism `𝒪_X ⟶ i_* 𝒪_Z` of structure sheaves is: local
surjectivity of a morphism of sheaves valued in a concrete category is that of the underlying
morphism of sheaves of sets, and forgetting commutativity does not change the latter. -/
theorem structureSheafHom_isLocallySurjective
    (hi : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    Sheaf.IsLocallySurjective (RingedSpaceModuleAdjunction.structureSheafHom i) := by
  have h : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) i.hom.c := hi
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  change Presheaf.IsLocallySurjective _ _
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact h

/-- The topos-level structure map of a morphism of ringed spaces is locally surjective as soon as
the comorphism of structure sheaves is: the two differ by the comparison of the topos-level direct
image of the structure sheaf of rings with its restriction along the continuous functor
`V ↦ i⁻¹ V`, which is an isomorphism. -/
theorem toposStructureRingMap_isLocallySurjective
    (hi : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    Sheaf.IsLocallySurjective (toposStructureRingMap i) := by
  let _ := structureSheafHom_isLocallySurjective i hi
  let _ : Sheaf.IsLocallySurjective (restrictionRingIso
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier)
      (Opens.map i.hom.base) (structureSheafRing Z)).inv :=
    Sheaf.isLocallySurjective_of_iso _
  exact Sheaf.isLocallySurjective_comp (RingedSpaceModuleAdjunction.structureSheafHom i)
    (restrictionRingIso (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Z.carrier) (Opens.map i.hom.base)
      (structureSheafRing Z)).inv

/-! ### Full faithfulness for ringed spaces and for schemes -/

/-- **The full-faithfulness half of Stacks 08M3 for a morphism of ringed spaces.** Pushforward of
sheaves of modules along a morphism of ringed spaces whose underlying continuous map is inducing
and whose comorphism of structure sheaves is locally surjective is fully faithful.

The hypotheses give exactly the two inputs of
`Stacks.ToposBridge.fullyFaithfulPushforwardModules` at the morphism of topoi presented by `i`,
and `Stacks.ToposBridge.pushforwardModulesIso` carries the conclusion over to the ordinary
pushforward. -/
def fullyFaithfulModulePushforward (hemb : Topology.IsInducing i.hom.base)
    (hsurj : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    (RingedSpaceModuleAdjunction.modulePushforward i).FullyFaithful := by
  refine Functor.FullyFaithful.ofIso ?_ (pushforwardModulesIso i)
  exact fullyFaithfulPushforwardModules (morphismOfTopoi i)
    (structureSheafRing Z) (toposStructureRingMap i)
    (fullyFaithfulPushforward i hemb) (toposStructureRingMap_isLocallySurjective i hsurj)

/-- **The full-faithfulness half of Stacks 08M3 for a closed immersion of schemes.** Pushforward
of sheaves of modules along a closed immersion of schemes is fully faithful.

The underlying map of spaces is a closed embedding, hence inducing, and the comorphism of
structure sheaves is locally surjective by
`Stacks.ClosedImmersion.isLocallySurjective_c_toShHom`. -/
def fullyFaithfulSchemeModulesPushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    (Scheme.Modules.pushforward i).FullyFaithful :=
  fullyFaithfulModulePushforward i.toLRSHom.toShHom
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).isInducing
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i)

/-- Pushforward of sheaves of modules along a closed immersion of schemes is full. -/
instance full_schemeModulesPushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] : (Scheme.Modules.pushforward i).Full :=
  (fullyFaithfulSchemeModulesPushforward i).full

/-- Pushforward of sheaves of modules along a closed immersion of schemes is faithful. -/
instance faithful_schemeModulesPushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] : (Scheme.Modules.pushforward i).Faithful :=
  (fullyFaithfulSchemeModulesPushforward i).faithful

end Stacks.ToposBridge

end
