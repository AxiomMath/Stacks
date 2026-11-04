module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullback

/-!
# The pullback of the meromorphic section determined by an ordinary section

Let `f : X ⟶ Y` be a morphism of locally ringed spaces for which pullbacks of meromorphic
functions are defined, and let `F` be a sheaf of `𝒪_Y`-modules. An ordinary section `t` of `F`
over an open `V` determines a meromorphic section of `F` over `V`, by the unit of extension of
scalars along `𝒪_Y ⟶ 𝒦_Y`. The pullback of meromorphic sections of [Stacks, Tag 02OY] part (1)
carries that meromorphic section to the one determined by the ordinary pullback of `t`:

  `f^*(toK t) = toK (f^* t)`   over `f ⁻¹ V`.

## Main results

* `AlgebraicGeometry.toPushforwardMeromorphicSectionSheaf_val_app` — the component of
  `AlgebraicGeometry.toPushforwardMeromorphicSectionSheaf` on a section is "pull back, then
  regard as meromorphic".
* `AlgebraicGeometry.meromorphicSectionSheafPullback_val_app_unit` — the displayed identity.

## Implementation notes

`RingedSpaceModuleAdjunction.modulePullback` is an abstract left adjoint and has no sectionwise
description, so "the pullback of `t`" means the component of the adjunction unit at `t`.

## References

* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (hf : PullbacksMeromorphicSections f)
  (F : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Y))

/-- The component of `AlgebraicGeometry.toPushforwardMeromorphicSectionSheaf` on a section:
pull the section back along the unit of `f^* ⊣ f_*`, then regard the result as a meromorphic
section by the unit of extension of scalars along `𝒪_X ⟶ 𝒦_X`. -/
theorem toPushforwardMeromorphicSectionSheaf_val_app (V : Opens Y) (t : F.val.obj (op V)) :
    (toPushforwardMeromorphicSectionSheaf f hf F).val.app (op V) t =
      ((LocallyRingedSpace.meromorphicExtendRestrictAdjunction X).unit.app
            ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)).val.app
          (op ((Opens.map f.base).obj V))
        (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          f.toShHom).unit.app F).val.app (op V) t) :=
  rfl

/-- **The pullback of the meromorphic section determined by an ordinary section is the
meromorphic section determined by its pullback.** The pullback morphism on sheaves of
meromorphic sections is the `𝒦_Y`-linear extension of the pullback of ordinary sections, so its
value on the image of `t` under the unit of extension of scalars is the image of the pullback of
`t` under the corresponding unit on the source. -/
theorem meromorphicSectionSheafPullback_val_app_unit (V : Opens Y) (t : F.val.obj (op V)) :
    (meromorphicSectionSheafPullback f hf F).val.app (op V)
        (((LocallyRingedSpace.meromorphicExtendRestrictAdjunction Y).unit.app F).val.app
          (op V) t) =
      ((LocallyRingedSpace.meromorphicExtendRestrictAdjunction X).unit.app
            ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)).val.app
          (op ((Opens.map f.base).obj V))
        (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          f.toShHom).unit.app F).val.app (op V) t) :=
  congrArg (fun g => g.val.app (op V) t)
    (unit_comp_meromorphicSectionSheafPullback f hf F)

end AlgebraicGeometry

end
