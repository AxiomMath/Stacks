module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Composition coherence for pullback and pushforward of sheaves of modules (Stacks 0096)

`StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace` constructs, for a morphism `f` of
ringed spaces, the adjoint pair `f^* ⊣ f_*` on sheaves of modules. This file records how that
pair behaves under composition of morphisms of ringed spaces:

`(f ≫ g)_* = f_* ⋙ g_*` and `(f ≫ g)^* ≅ g^* ⋙ f^*`.

The pushforward law is an isomorphism of functors whose components are identity morphisms — in
fact the two functors are definitionally equal, since the pushforward of sheaves of modules is
given on sections by `(f_* F)(V) = F(f⁻¹ V)` and taking preimages is literally associative. The
pullback law is then forced: `(f ≫ g)^*` and `g^* ⋙ f^*` are both left adjoint to the same
functor, so uniqueness of left adjoints produces a canonical isomorphism between them, and it is
characterised — not computed — by the mate correspondence
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom`.

The second half of the file is the same coherence for the *structure sheaf* read as a sheaf of
modules over itself. `RingedSpaceModuleAdjunction.structureSheafModuleHom` is the map
`𝒪_Y ⟶ f_* 𝒪_X` in the category of sheaves of `𝒪_Y`-modules; it is multiplicative in `f` on the
nose, which is what makes the ideal sheaf of a composite closed immersion comparable with the
ideal sheaves of its factors.

## Main definitions

* `RingedSpaceModuleAdjunction.modulePushforwardComp` is the composition law
  `f_* ⋙ g_* ≅ (f ≫ g)_*` for pushforward.
* `RingedSpaceModuleAdjunction.modulePullbackComp` is the composition law
  `(f ≫ g)^* ≅ g^* ⋙ f^*` for pullback.
* `RingedSpaceModuleAdjunction.modulePushforwardId` and
  `RingedSpaceModuleAdjunction.modulePullbackId` are the corresponding unit laws
  `(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`.
* `RingedSpaceModuleAdjunction.modulePullbackCongr` compares the pullbacks along two
  equal morphisms.
* `RingedSpaceModuleAdjunction.structureSheafModuleHom` is the structure-sheaf map
  `𝒪_Y ⟶ f_* 𝒪_X` as a morphism of sheaves of modules.
* `RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` is its left-adjoint transpose
  `f^* 𝒪_Y ⟶ 𝒪_X`.

## Main results

* `RingedSpaceModuleAdjunction.opensMap_comp` and
  `RingedSpaceModuleAdjunction.structureSheafHom_comp`: the two data defining the
  pushforward are multiplicative in `f` on the nose.
* `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom`: the characterising
  property of `modulePullbackComp`. Under the mate correspondence between natural
  transformations of left adjoints and of right adjoints, it corresponds to
  `modulePushforwardComp`. Everything one needs to know about the pullback composition
  isomorphism — in particular its effect on the units of the adjunctions, via
  `CategoryTheory.unit_conjugateEquiv_symm` — follows from this, and no description of the
  underlying maps on sections is ever required.
* `RingedSpaceModuleAdjunction.structureSheafModuleHom_comp`: the cocycle condition
  `𝒪_Z ⟶ (f ≫ g)_* 𝒪_X` equals `𝒪_Z ⟶ g_* 𝒪_Y ⟶ g_* f_* 𝒪_X`.

## Implementation notes

The whole file is an instantiation of Mathlib's composition coherence for sheaves of modules on
a *site*, `CategoryTheory.SheafOfModules.pushforwardComp` and
`CategoryTheory.SheafOfModules.pullbackComp`, at the two data a morphism of ringed spaces
supplies: the inverse-image functor `RingedSpaceModuleAdjunction.opensMap` on opens and
the structure-sheaf map `RingedSpaceModuleAdjunction.structureSheafHom`. The point of the
file is that both of these are multiplicative *by `rfl`*, so no comparison isomorphism of sites
intervenes and the instantiation is direct.

`RingedSpaceModuleAdjunction.pushforward_structureSheafHom_isRightAdjoint` is the
existence of the left adjoint registered as an instance for
`CategoryTheory.SheafOfModules.pushforward (structureSheafHom f)` rather than for
`modulePushforward f`. This is deliberate: Mathlib's coherence statements are phrased in terms of
`CategoryTheory.SheafOfModules.pullback` and instance resolution unfolds only at reducible
transparency, so an instance stated for `modulePushforward f` is not found. With the instance in
this form the `letI`s that `modulePullback` carries are unnecessary at every point of use.

For the same reason `RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` and
`RingedSpaceModuleAdjunction.structureSheafModuleHom` exist at all: they are
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` and
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` with their types restated through
`modulePullback` and `modulePushforward`. Mixing the two vocabularies inside one composite
morphism produces a term that is type-incorrect at `implicit` transparency, which makes every
subsequent `rw` fail; keeping each statement in a single vocabulary avoids that.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0095](https://stacks.math.columbia.edu/tag/0095)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor

universe u

namespace RingedSpaceModuleAdjunction

/-! ### The two data of the pushforward are multiplicative -/

variable {X Y Z : RingedSpace.{u, u}}

/-- **Taking preimages of opens is associative.** The inverse-image functor on opens attached to
a composite of morphisms of ringed spaces is the composite of the inverse-image functors, in the
opposite order, and this is an equality of functors rather than merely an isomorphism. -/
theorem opensMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    opensMap (f ≫ g) = opensMap g ⋙ opensMap f :=
  rfl

/-- **The structure-sheaf map is multiplicative.** Under `opensMap_comp`, the datum
`f^♯ : 𝒪_Z ⟶ (f ≫ g)_* 𝒪_X` of a composite morphism of ringed spaces is the datum of `g`
followed by the pushforward along `g` of the datum of `f`. -/
theorem structureSheafHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheafHom (f ≫ g) =
      structureSheafHom g ≫ ((opensMap g).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Z.carrier) (Opens.grothendieckTopology Y.carrier)).map
          (structureSheafHom f) :=
  rfl

/-! ### Composition coherence -/

/-- **Pushforward is multiplicative, `f_* ⋙ g_* ≅ (f ≫ g)_*`.** For sheaves of modules on
ringed spaces the two functors are definitionally equal: on sections both are
`V ↦ F((f ≫ g)⁻¹ V)` by `opensMap_comp`, with the same module structure by
`structureSheafHom_comp`. -/
noncomputable def modulePushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward f ⋙ modulePushforward g ≅ modulePushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp (structureSheafHom g) (structureSheafHom f)

/-- The components of `modulePushforwardComp` are identity morphisms. -/
@[simp]
theorem modulePushforwardComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforwardComp f g).hom.app F = 𝟙 ((modulePushforward (f ≫ g)).obj F) :=
  rfl

/-- The components of the inverse of `modulePushforwardComp` are identity morphisms. -/
@[simp]
theorem modulePushforwardComp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforwardComp f g).inv.app F = 𝟙 ((modulePushforward (f ≫ g)).obj F) :=
  rfl

/-- Pushforward of sheaves of modules sends the zero morphism to the zero morphism. The
pushforward does not change the underlying maps on sections, only the opens they are indexed
by. -/
@[simp]
theorem modulePushforward_map_zero (f : X ⟶ Y) (F G : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward f).map (0 : F ⟶ G) = 0 :=
  rfl

/-- **Pushforward along the identity is the identity**, `(𝟙 X)_* ≅ 𝟭`. As with
`modulePushforwardComp` the two functors are definitionally equal, since `opensMap (𝟙 X) = 𝟭` and
`structureSheafHom (𝟙 X) = 𝟙`. -/
noncomputable def modulePushforwardId (X : RingedSpace.{u, u}) :
    modulePushforward (𝟙 X) ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  SheafOfModules.pushforwardId (structureSheafRing X)

/-- The components of the inverse of `modulePushforwardId` are identity morphisms. -/
theorem modulePushforwardId_inv_app (X : RingedSpace.{u, u})
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforwardId X).inv.app F = 𝟙 F :=
  rfl

/-- **Pullback along the identity is the identity**, `(𝟙 X)^* ≅ 𝟭`. Both functors are left
adjoint to `𝟭`, by `modulePushforwardId`. -/
noncomputable def modulePullbackId (X : RingedSpace.{u, u}) :
    modulePullback (𝟙 X) ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  SheafOfModules.pullbackId (structureSheafRing X)

/-- **Pullback is multiplicative, `(f ≫ g)^* ≅ g^* ⋙ f^*`.** Both functors are left adjoint to
`f_* ⋙ g_* = (f ≫ g)_*`, by `modulePushforwardComp`, so uniqueness of left adjoints supplies a
canonical isomorphism. See `conjugateEquiv_modulePullbackComp_hom` for its characterisation. -/
noncomputable def modulePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback (f ≫ g) ≅ modulePullback g ⋙ modulePullback f :=
  (SheafOfModules.pullbackComp (structureSheafHom g) (structureSheafHom f)).symm

/-- **The characterisation of `modulePullbackComp`.** Under the mate correspondence
`CategoryTheory.conjugateEquiv` between natural transformations of left adjoints and natural
transformations of the corresponding right adjoints, the pullback composition isomorphism
corresponds to the pushforward composition isomorphism.

This determines `modulePullbackComp` completely, and is the form in which it is used: combined
with `CategoryTheory.unit_conjugateEquiv_symm` it computes the effect of the isomorphism on the
units of the two adjunctions, which is all a consumer needs. -/
theorem conjugateEquiv_modulePullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((modulePullbackPushforwardAdjunction g).comp
        (modulePullbackPushforwardAdjunction f))
      (modulePullbackPushforwardAdjunction (f ≫ g)) (modulePullbackComp f g).hom =
      (modulePushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv (structureSheafHom g) (structureSheafHom f)

/-- Pullbacks along equal morphisms of ringed spaces are isomorphic. -/
noncomputable def modulePullbackCongr {f g : X ⟶ Y} (h : f = g) :
    modulePullback f ≅ modulePullback g :=
  eqToIso (congrArg modulePullback h)

/-! ### The structure sheaf as a sheaf of modules over itself -/

/-- The structure-sheaf map `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` of a morphism of ringed spaces, read as a
morphism of sheaves of `𝒪_Y`-modules between the two structure sheaves regarded as modules over
themselves. -/
noncomputable abbrev structureSheafModuleHom (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheafRing Y) ⟶
      (modulePushforward f).obj (SheafOfModules.unit (structureSheafRing X)) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)

/-- **The cocycle condition for the structure-sheaf map.** The structure-sheaf map of a
composite, read as a morphism of sheaves of modules, is the structure-sheaf map of the second
factor followed by the pushforward of the structure-sheaf map of the first. The two sides are
definitionally equal by `structureSheafHom_comp`. -/
theorem structureSheafModuleHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheafModuleHom (f ≫ g) =
      structureSheafModuleHom g ≫ (modulePushforward g).map (structureSheafModuleHom f) :=
  rfl

/-- The left-adjoint transpose `f^* 𝒪_Y ⟶ 𝒪_X` of the structure-sheaf map. -/
noncomputable def modulePullbackUnitToUnit (f : X ⟶ Y) :
    (modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)) ⟶
      SheafOfModules.unit (structureSheafRing X) :=
  SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)

/-- `modulePullbackUnitToUnit` is the transpose of the structure-sheaf map: applying the hom-set
bijection of `f^* ⊣ f_*` to it returns `structureSheafModuleHom f`. -/
@[simp]
theorem homEquiv_modulePullbackUnitToUnit (f : X ⟶ Y) :
    (modulePullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackUnitToUnit f) =
      structureSheafModuleHom f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end RingedSpaceModuleAdjunction

end
