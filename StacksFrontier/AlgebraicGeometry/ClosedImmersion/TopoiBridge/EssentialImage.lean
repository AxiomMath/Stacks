module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubtopos.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of pushforward along a closed immersion of schemes

Let `i : Z ⟶ X` be a closed immersion of schemes. A sheaf of `𝒪_X`-modules is a direct image
along `i` exactly when the sectionwise kernel of the structure map `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z`
annihilates it. This is the essential-image half of Stacks 08M3, which the repository proves for a
closed immersion of ringed topoi, carried down to schemes.

## Main results

* `Stacks.ToposBridge.essImage_pushforwardModules_iff_of_iso` — the topos-level essential-image
  criterion, transported across a natural isomorphism of the direct-image functor.
* `Stacks.ToposBridge.essImage_schemeModulesPushforward_iff` — the essential-image half of
  Stacks 08M3 for a closed immersion of schemes.

## Implementation notes

Both inputs of the topos-level criterion are available for a closed immersion of schemes: the
presented morphism of topoi is a closed immersion of topoi by
`Stacks.ClosedSubtopos.isClosedImmersion_morphismOfTopoi_of_scheme`, and the topos-level structure
map is locally surjective by `Stacks.ToposBridge.toposStructureRingMap_isLocallySurjective` applied
to `Stacks.ClosedImmersion.isLocallySurjective_c_toShHom`. The conclusion is carried from
`Stacks.Sheaves.PushforwardEssentialImage.pushforwardModules` to
`AlgebraicGeometry.Scheme.Modules.pushforward` along
`Stacks.ToposBridge.schemePushforwardModulesIso`, the essential image being invariant under a
natural isomorphism.

That transport is stated over an abstract site and only then instantiated, for the reason recorded
in `Stacks.ToposBridge.fullyFaithfulPushforwardModules`: at a concrete site the universe levels of
`CategoryTheory.SheafOfModules` are numerals while its category instance carries them inside a
`max`, so instance search for the category of sheaves of modules does not fire there, whereas over
an abstract site the levels stay generic and it does.

The annihilation condition is stated with the sectionwise kernel of the structure map rather than
with the kernel ideal sheaf `AlgebraicGeometry.Scheme.Hom.ker`, because it quantifies over every
open of `X` whereas `AlgebraicGeometry.Scheme.Hom.ker_apply` computes that ideal only over affine
opens. This is the source's own phrasing: 08M3 takes `I` to be the sectionwise kernel of `i^♯`.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.PushforwardEssentialImage

universe ww vv uu vv' uu' u

namespace Stacks.ToposBridge

/-! ### The criterion across an isomorphism of the direct-image functor -/

section General

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]

/-- **The essential-image half of Stacks 08M3, across an isomorphism.** If the direct image on
sheaves of modules determined by a closed immersion of topoi `f` and a locally surjective
structure map `α` is naturally isomorphic to a functor `T`, then a sheaf of modules lies in the
essential image of `T` exactly when the sectionwise kernel of `α` annihilates it.

The essential image of a functor is invariant under a natural isomorphism
(`CategoryTheory.Functor.essImage_eq_of_natIso`), so this is
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`
read through the isomorphism. -/
theorem essImage_pushforwardModules_iff_of_iso
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))
    (O : Sheaf J RingCat.{ww}) {O' : Sheaf K RingCat.{ww}}
    (α : O' ⟶ pushforwardRingSheaf f O)
    (hfc : MorphismOfTopoi.IsClosedImmersion f) (hα : Sheaf.IsLocallySurjective α)
    {T : _root_.SheafOfModules.{ww} O ⥤ _root_.SheafOfModules.{ww} O'}
    (e : pushforwardModules f O α ≅ T)
    (G : _root_.SheafOfModules.{ww} O') :
    T.essImage G ↔
      ∀ (U : Dᵒᵖ) (a : O'.obj.obj U), a ∈ RingHom.ker (α.hom.app U).hom →
        ∀ m : G.val.obj U, a • m = 0 := by
  have := hα
  rw [← Functor.essImage_eq_of_natIso e]
  exact essImage_pushforwardModules_iff_of_isClosedImmersion f O hfc α G

end General

/-! ### The scheme-level clause -/

/-- **The essential-image half of Stacks 08M3 for a closed immersion of schemes.** A sheaf of
`𝒪_X`-modules lies in the essential image of pushforward along a closed immersion `i : Z ⟶ X`
exactly when the sectionwise kernel of the structure map of `i` annihilates it.

This is `Stacks.ToposBridge.essImage_pushforwardModules_iff_of_iso` at the morphism of topoi
presented by `i`, whose closed-immersion and local-surjectivity hypotheses hold for a closed
immersion of schemes, transported along `Stacks.ToposBridge.schemePushforwardModulesIso`. -/
@[stacks 08M3 "essential_image, for a closed immersion of schemes"]
theorem essImage_schemeModulesPushforward_iff {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (G : X.Modules) :
    (Scheme.Modules.pushforward i).essImage G ↔
      ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.ringCatSheaf.obj.obj U),
        a ∈ RingHom.ker ((toposStructureRingMap i.toLRSHom.toShHom).hom.app U).hom →
          ∀ m : G.val.obj U, a • m = 0 :=
  essImage_pushforwardModules_iff_of_iso (morphismOfTopoi i.toLRSHom.toShHom)
    (structureSheafRing Z.toRingedSpace)
    (toposStructureRingMap i.toLRSHom.toShHom)
    (Stacks.ClosedSubtopos.isClosedImmersion_morphismOfTopoi_of_scheme i)
    (toposStructureRingMap_isLocallySurjective i.toLRSHom.toShHom
      (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i))
    (schemePushforwardModulesIso i) G

end Stacks.ToposBridge

end
