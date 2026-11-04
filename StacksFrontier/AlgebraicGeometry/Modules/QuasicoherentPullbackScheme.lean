module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Pullback of a quasi-coherent module along a morphism of schemes

Specialisation of the ringed-space statement
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` (Stacks 01BG) to a morphism
of schemes, in the vocabulary of `AlgebraicGeometry.Scheme.Modules`.

## Main results

* `Stacks.Modules.isQuasicoherent_pullback`, and its instance form
  `Stacks.Modules.instIsQuasicoherentPullbackObj`: the pullback of a quasi-coherent module
  along an *arbitrary* morphism of schemes is quasi-coherent.
* `Stacks.Modules.pullbackQcoh` is the induced functor between the categories of
  quasi-coherent modules.

## Implementation notes

No mathematics happens here: for a morphism of schemes `f : X ⟶ Y` the comparison between the
scheme-level and the ringed-space-level pullback is definitional. Concretely,
`structureSheafRing Y.toRingedSpace`, `structureSheafHom f.toLRSHom.toShHom` and
`(RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj M` are definitionally
`Y.ringCatSheaf`, `f.toRingCatSheafHom` and `(Scheme.Modules.pullback f).obj M`, because
`Scheme.ringCatSheaf` and `Scheme.Hom.toRingCatSheafHom` are built by the same two formulas
(`sheafCompose (forget₂ CommRingCat RingCat)` and `whiskerRight f.c _`), and
`Scheme.Modules.pullback` is `SheafOfModules.pullback` of that morphism.

Mathlib already knows the affine and open-immersion cases of this statement, in the forms
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` plus `essImage_tilde` and
`Scheme.Modules.restrictFunctorIsoPullback`; the content of Stacks 01BG is that no
hypothesis on `f` at all is needed.

Note that there is no counterpart for pushforward: `f_*` preserves quasi-coherence only under
a hypothesis on `f` (quasi-compact and quasi-separated).

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 01BG for schemes.** The pullback of a quasi-coherent module along an arbitrary
morphism of schemes is quasi-coherent. This is the specialisation of
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` along the definitional
identification of `Scheme.Modules.pullback f` with pullback on the underlying ringed
spaces. -/
lemma isQuasicoherent_pullback (M : Y.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
    X.toLocallyRingedSpace.toRingedSpace Y.toLocallyRingedSpace.toRingedSpace
    f.toLRSHom.toShHom M hM

/-- **Stacks 01BG for schemes**, in instance form, so that quasi-coherence of a pullback is
found by instance search. -/
instance instIsQuasicoherentPullbackObj (M : Y.Modules) [h : M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  isQuasicoherent_pullback f M h

/-- Pullback of quasi-coherent modules along an arbitrary morphism of schemes, as a functor
between the full subcategories of quasi-coherent modules. -/
noncomputable def pullbackQcoh :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f)
    fun M ↦ isQuasicoherent_pullback f M.obj M.property

/-- Forgetting quasi-coherence identifies `pullbackQcoh` with pullback of modules. -/
lemma pullbackQcoh_comp_ι :
    pullbackQcoh f ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f := rfl

end Stacks.Modules

end
