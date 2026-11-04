module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pullback of meromorphic sections

Let `f : X ⟶ Y` be a morphism of locally ringed spaces for which pullbacks of meromorphic
functions are defined, and let `F` be a sheaf of `𝒪_Y`-modules. Pulling back a numerator and
a denominator separately carries a meromorphic section of `F` to a meromorphic section of
`f^* F`; equivalently, the sheaf `𝒦_Y(F)` of meromorphic sections of `F` maps canonically to
the direct image of `𝒦_X(f^* F)` over the pullback morphism `𝒦_Y ⟶ f_* 𝒦_X` of sheaves of
meromorphic functions.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.ringCatSheaf`,
  `AlgebraicGeometry.LocallyRingedSpace.totalQuotientRingCatSheaf` and
  `AlgebraicGeometry.LocallyRingedSpace.toTotalQuotientRingCatSheaf`: the structure sheaf, the
  sheaf of meromorphic functions, and the map between them, as `RingCat`-valued sheaves of
  rings, the form over which sheaves of modules are taken.
* `AlgebraicGeometry.totalQuotientRingCatSheafPullback`: the pullback morphism
  `𝒦_Y ⟶ f_* 𝒦_X` on sheaves of meromorphic functions, as a morphism of `RingCat`-valued
  sheaves of rings.
* `AlgebraicGeometry.meromorphicSectionSheafPullback`: the induced morphism
  `𝒦_Y(F) ⟶ f_* 𝒦_X(f^* F)`.
* `AlgebraicGeometry.pullbackMeromorphicSection`: the canonical pullback map
  `Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^* F))` on meromorphic sections.
* `PresheafOfModules.sectionsOfTop`: the global section of a presheaf of modules on a space
  determined by a value over an open set containing the whole space.

## Main results

* `AlgebraicGeometry.toTotalQuotient_comp_totalQuotientRingCatSheafPullback`: the square
  relating the two localization maps `𝒪 ⟶ 𝒦` to the two pullback maps commutes. This is what
  makes a sheaf of meromorphic functions on `X` an `𝒪_Y`-module in a single way, and hence
  what the pullback of meromorphic sections is built from.
* `AlgebraicGeometry.unit_comp_meromorphicSectionSheafPullback`: the pullback morphism on
  sheaves of meromorphic sections restricts along the unit of extension of scalars to the
  pullback of ordinary sections, which by the adjunction determines it uniquely.

## Implementation notes

The construction is the adjunct of a morphism of `𝒪_Y`-modules: `F` maps to the direct image
of its pullback by the unit of `f^* ⊣ f_*`, and the pullback maps to its sheaf of meromorphic
sections by the unit of extension of scalars along `𝒪_X ⟶ 𝒦_X`. The resulting morphism lands
in a direct image taken over the composite `𝒪_Y ⟶ f_* 𝒪_X ⟶ f_* 𝒦_X`, whereas extension of
scalars along `𝒪_Y ⟶ 𝒦_Y` produces one taken over `𝒪_Y ⟶ 𝒦_Y ⟶ f_* 𝒦_X`; the two composites
agree by the commuting square, and `CategoryTheory.SheafOfModules.pushforwardCongr` transports
between them. Direct image along a continuous functor absorbs restriction of scalars on either
side, so both targets are literally direct images over those composites.

A global section of a direct image is read off at the top open set: its component there is a
section over the preimage of the whole target space, which is the whole source space, and
`PresheafOfModules.sectionsOfTop` spreads that value back over all open sets.

Everything is stated for sheaves of modules in the universe of the space, which is the
universe in which pullback of sheaves of modules along a morphism of ringed spaces is
available.

## References

* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace PresheafOfModules

/-- The global section of a presheaf of modules on a space obtained from a value over an open
set containing the whole space, by restricting that value to every open set. -/
noncomputable def sectionsOfTop {Z : TopCat.{u}} {R : (Opens Z)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {W : Opens Z} (hW : ⊤ ≤ W) (m : M.obj (op W)) : M.sections :=
  PresheafOfModules.sectionsMk (fun _ => M.map (homOfLE (le_top.trans hW)).op m)
    (fun _ _ i => (M.map_comp_apply _ i m).symm.trans
      (M.congr_map_apply (Subsingleton.elim _ _) m))

end PresheafOfModules

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- The structure sheaf of a locally ringed space as a sheaf of `RingCat`-valued rings; this
is the form over which sheaves of modules on the space are taken. -/
noncomputable abbrev ringCatSheaf (Z : LocallyRingedSpace.{u}) :
    Sheaf (Opens.grothendieckTopology Z.toPresheafedSpace) RingCat.{u} :=
  Stacks.Sheaves.Differentials.ringSheaf (C := Opens Z.toPresheafedSpace)
    (J := Opens.grothendieckTopology Z.toPresheafedSpace) Z.sheaf

/-- The sheaf of meromorphic functions of a locally ringed space as a sheaf of `RingCat`-valued
rings. -/
noncomputable abbrev totalQuotientRingCatSheaf (Z : LocallyRingedSpace.{u}) :
    Sheaf (Opens.grothendieckTopology Z.toPresheafedSpace) RingCat.{u} :=
  Stacks.Sheaves.Differentials.ringSheaf (C := Opens Z.toPresheafedSpace)
    (J := Opens.grothendieckTopology Z.toPresheafedSpace) (totalQuotientSheaf Z.sheaf)

/-- The canonical map `𝒪_Z ⟶ 𝒦_Z` from regular to meromorphic functions, as a morphism of
`RingCat`-valued sheaves of rings. -/
@[ega "IV 20.1.4"]
noncomputable abbrev toTotalQuotientRingCatSheaf (Z : LocallyRingedSpace.{u}) :
    ringCatSheaf Z ⟶ totalQuotientRingCatSheaf Z :=
  (sheafCompose (Opens.grothendieckTopology Z.toPresheafedSpace)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (toTotalQuotientSheaf Z.sheaf)

end LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- Direct image of `RingCat`-valued sheaves of rings along the morphism of sites induced by a
morphism of locally ringed spaces. -/
noncomputable abbrev ringCatSheafPushforward :
    Sheaf (Opens.grothendieckTopology X.toPresheafedSpace) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y.toPresheafedSpace) RingCat.{u} :=
  (Opens.map f.base).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y.toPresheafedSpace)
    (Opens.grothendieckTopology X.toPresheafedSpace)

/-- The pullback morphism `𝒦_Y ⟶ f_* 𝒦_X` on sheaves of meromorphic functions, as a morphism
of `RingCat`-valued sheaves of rings. It exists because pullbacks of meromorphic functions are
defined for `f`. -/
@[ega "IV 21.8.3"]
noncomputable def totalQuotientRingCatSheafPullback (hf : PullbacksMeromorphicSections f) :
    LocallyRingedSpace.totalQuotientRingCatSheaf Y ⟶
      (ringCatSheafPushforward f).obj (LocallyRingedSpace.totalQuotientRingCatSheaf X) :=
  ObjectProperty.homMk (Functor.whiskerRight
    (Stacks.Meromorphic.totalQuotientSheafPullback f hf).hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- Pulling a regular function back and then regarding it as meromorphic is the same as
regarding it as meromorphic and then pulling back: the square relating `𝒪 ⟶ 𝒦` on both spaces
to the two pullback morphisms commutes. -/
@[ega "IV 21.8.3" "partial"]
theorem toTotalQuotient_comp_totalQuotientRingCatSheafPullback
    (hf : PullbacksMeromorphicSections f) :
    RingedSpaceModuleAdjunction.structureSheafHom f.toShHom ≫
        (ringCatSheafPushforward f).map (LocallyRingedSpace.toTotalQuotientRingCatSheaf X) =
      LocallyRingedSpace.toTotalQuotientRingCatSheaf Y ≫
        totalQuotientRingCatSheafPullback f hf :=
  .symm <| Sheaf.hom_ext <| NatTrans.ext <| funext fun V =>
    congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map (k.app V))
      (Stacks.Meromorphic.toTotalQuotientSheaf_comp_totalQuotientSheafPullback f hf)

/-- Extension of scalars along `𝒪_Z ⟶ 𝒦_Z` is left adjoint to restriction of scalars; this is
the adjunction at which the pullback of meromorphic sections is read. -/
noncomputable abbrev LocallyRingedSpace.meromorphicExtendRestrictAdjunction
    (Z : LocallyRingedSpace.{u}) :
    Stacks.Sheaves.ChangeOfRings.changeOfRings
        (Opens.grothendieckTopology Z.toPresheafedSpace) (toTotalQuotientSheaf Z.sheaf) ⊣
      SheafOfModules.restrictScalars (LocallyRingedSpace.toTotalQuotientRingCatSheaf Z) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology Z.toPresheafedSpace) (toTotalQuotientSheaf Z.sheaf).hom
    (LocallyRingedSpace.ringCatSheaf Z).property
    (LocallyRingedSpace.totalQuotientRingCatSheaf Z).property

variable (hf : PullbacksMeromorphicSections f)
  (F : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Y))

/-- The morphism of sheaves of `𝒪_Y`-modules sending a section of `F` to the meromorphic
section of `f^* F` determined by its pullback, with values read over preimages of open sets of
`Y`. It is the unit of `f^* ⊣ f_*` followed by the direct image of the unit of extension of
scalars along `𝒪_X ⟶ 𝒦_X`, transported along the commuting square. -/
noncomputable def toPushforwardMeromorphicSectionSheaf :
    F ⟶ (SheafOfModules.restrictScalars
        (LocallyRingedSpace.toTotalQuotientRingCatSheaf Y)).obj
      ((SheafOfModules.pushforward (totalQuotientRingCatSheafPullback f hf)).obj
        (meromorphicSectionSheaf X.sheaf
          ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F))) :=
  ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toShHom).unit.app F ≫
      (SheafOfModules.pushforward
        (RingedSpaceModuleAdjunction.structureSheafHom f.toShHom)).map
          ((LocallyRingedSpace.meromorphicExtendRestrictAdjunction X).unit.app
            ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F))) ≫
    (SheafOfModules.pushforwardCongr
      (toTotalQuotient_comp_totalQuotientRingCatSheafPullback f hf)).hom.app _

/-- The morphism `𝒦_Y(F) ⟶ f_* 𝒦_X(f^* F)` of sheaves of `𝒦_Y`-modules: the `𝒦_Y`-linear
extension of the map carrying a section of `F` to the pullback of that section, viewed as a
meromorphic section of `f^* F`. -/
noncomputable def meromorphicSectionSheafPullback :
    meromorphicSectionSheaf Y.sheaf F ⟶
      (SheafOfModules.pushforward (totalQuotientRingCatSheafPullback f hf)).obj
        (meromorphicSectionSheaf X.sheaf
          ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)) :=
  ((LocallyRingedSpace.meromorphicExtendRestrictAdjunction Y).homEquiv F _).symm
    (toPushforwardMeromorphicSectionSheaf f hf F)

/-- The pullback morphism on sheaves of meromorphic sections is the `𝒦_Y`-linear extension of
the pullback of ordinary sections: restricting it along the unit of extension of scalars
returns `AlgebraicGeometry.toPushforwardMeromorphicSectionSheaf`. By the adjunction this
property determines the morphism uniquely. -/
theorem unit_comp_meromorphicSectionSheafPullback :
    (LocallyRingedSpace.meromorphicExtendRestrictAdjunction Y).unit.app F ≫
        (SheafOfModules.restrictScalars
          (LocallyRingedSpace.toTotalQuotientRingCatSheaf Y)).map
            (meromorphicSectionSheafPullback f hf F) =
      toPushforwardMeromorphicSectionSheaf f hf F :=
  ((LocallyRingedSpace.meromorphicExtendRestrictAdjunction Y).homEquiv_unit
      (f := meromorphicSectionSheafPullback f hf F)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The canonical pullback map on meromorphic sections.** When pullbacks of meromorphic
functions are defined for `f`, a meromorphic section of a sheaf of `𝒪_Y`-modules `F` pulls
back to a meromorphic section of `f^* F`: apply the morphism `𝒦_Y(F) ⟶ f_* 𝒦_X(f^* F)` and
read the resulting global section over the whole of `X`. -/
@[stacks 02OY "part (1)", ega "IV 20.1.11" "mero section pullback"]
noncomputable def pullbackMeromorphicSection (s : MeromorphicSection Y.sheaf F) :
    MeromorphicSection X.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F) :=
  PresheafOfModules.sectionsOfTop _ (W := (Opens.map f.base).obj ⊤) (fun _ _ => trivial)
    ((SheafOfModules.sectionsMap (meromorphicSectionSheafPullback f hf F) s).1 (op ⊤))

end AlgebraicGeometry
