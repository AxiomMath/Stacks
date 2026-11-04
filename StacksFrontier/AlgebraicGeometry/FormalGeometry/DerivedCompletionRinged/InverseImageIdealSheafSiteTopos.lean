module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare

/-!
# The two constructions of `f^{-1}ℐ · 𝒪_X` agree

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites and `ℐ ⊂ 𝒪` a sheaf of ideals.
Section 52.7 of the Stacks project builds out of `ℐ` the ideal sheaf `ℐ' = f^{-1}ℐ · 𝒪_X` of `𝒪'`.
This repository has two constructions of it, over the two presentations of the morphism:

* `AlgebraicGeometry.RingedSite.inverseImageIdealSheaf`, built from `SheafOfModules.pullback` over
  the structure map `AlgebraicGeometry.RingedToposSiteHom.fSharpRing` of the site-presented
  morphism, with the comparison `f^*𝒪 ⟶ 𝒪'` spelled as `SheafOfModules.pullbackObjUnitToUnit`;
* `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf`, built from
  `AlgebraicGeometry.RingedToposHom.pullbackModules` over the two-field morphism of ringed topoi
  of [Stacks, Tag 01D3] part (2), with the comparison spelled as
  `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`.

They are *not* definitionally equal — the two pullback functors are different functors, compared
only by `AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`, and the two comparison maps are
different morphisms. This file proves they agree.

## Why no compatibility of the two unit comparisons is proved

One might expect the proof to identify the two comparisons `f^*𝒪 ⟶ 𝒪'` across
`pullbackToposIso`. That identification is **false**, and the module documentation of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedPullbackQuasicoherent.lean` records why:
`pullbackToposIso` is assembled from two applications of
`CategoryTheory.Adjunction.leftAdjointUniq`, hence from a `Classical.choice` of left adjoint, and
the automorphism of `𝒪'` by which the two comparisons differ cannot be pinned down.

Nothing has to be pinned down. Both comparisons are invertible —
`AlgebraicGeometry.RingedSite.isIso_pullbackObjUnitToUnit_fSharpRing` and
`AlgebraicGeometry.RingedToposHom.isIso_pullbackUnitStructureMap` — so they differ by an
automorphism of `SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`, and an image
subsheaf is insensitive to an automorphism of the unit object, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso`. That is exactly the manoeuvre
`AlgebraicGeometry.RingedSite.overIdeal_inverseImageIdealSheaf` already performs for the
restriction of `ℐ'` to a slice site, and it is performed here against the same lemma.

## Main definitions and results

* `AlgebraicGeometry.RingedSite.toposUnitDiscrepancy`: the automorphism of `𝒪'` by which the two
  comparisons `f^*𝒪 ⟶ 𝒪'` differ.
* `AlgebraicGeometry.RingedSite.inverseImageIdealMap_ringedToposHom`: the canonical map
  `f^*ℐ ⟶ 𝒪'` of the morphism of ringed topoi is the one of the morphism of ringed sites, up to
  `pullbackToposIso` at `ℐ` on the source and that automorphism on the target.
* `AlgebraicGeometry.RingedSite.inverseImageIdealSheaf_ringedToposHom`: **the two constructions of
  `ℐ' = f^{-1}ℐ · 𝒪_X` agree**, with no hypothesis on `ℐ` and none on `f` beyond its being a
  morphism of ringed sites.

## Deliberately untagged

Section 52.7 introduces `f^{-1}ℐ · 𝒪_X` in passing rather than as a numbered statement, and
neither of the two constructions carries an attribute.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}}
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedSite.Hom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))

/-- **The automorphism of `𝒪'` by which the two comparisons `f^*𝒪 ⟶ 𝒪'` differ.** One is
`SheafOfModules.pullbackObjUnitToUnit` over the site-presented morphism, the other is
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` over the two-field morphism of ringed
topoi, read across `AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`. Both are invertible, so
they differ by an automorphism of `𝒪'`, which is what this is.

It is not the identity, and nothing says it should be: `pullbackToposIso` is built from
`CategoryTheory.Adjunction.leftAdjointUniq`, hence from a choice of left adjoint. Every statement
below is insensitive to it, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso`. -/
def toposUnitDiscrepancy :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (@asIso _ _ _ _ _ (isIso_pullbackObjUnitToUnit_fSharpRing f)).symm ≪≫
    (f.pullbackToposIso.app
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm ≪≫
    @asIso _ _ _ _ _
      (AlgebraicGeometry.RingedToposHom.isIso_pullbackUnitStructureMap f.ringedToposHom)

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of the morphism of ringed topoi is the one of the morphism of
ringed sites**, up to `AlgebraicGeometry.RingedSite.Hom.pullbackToposIso` on the source and the
automorphism `AlgebraicGeometry.RingedSite.toposUnitDiscrepancy` of `𝒪'` on the target. This is
the definition of that automorphism, rearranged. -/
theorem pullbackUnitStructureMap_ringedToposHom :
    AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f.ringedToposHom =
      (f.pullbackToposIso.app
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫
        SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingedToposSiteHom.fSharpRing ≫
          (toposUnitDiscrepancy f).hom :=
  ((f.pullbackToposIso.app
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom_inv_id_assoc
      (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f.ringedToposHom)).symm.trans
    (congrArg
      (fun m ↦ (f.pullbackToposIso.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫ m)
      ((@asIso _ _ _ _ _ (isIso_pullbackObjUnitToUnit_fSharpRing f)).hom_inv_id_assoc
        ((f.pullbackToposIso.app
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).inv ≫
          AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f.ringedToposHom)).symm)

/-- **The canonical map `f^*ℐ ⟶ 𝒪'` of the morphism of ringed topoi is the one of the morphism of
ringed sites**, through `AlgebraicGeometry.RingedSite.Hom.pullbackToposIso` at `ℐ` on the source
and the automorphism `AlgebraicGeometry.RingedSite.toposUnitDiscrepancy` of `𝒪'` on the target.

The comparison of pullbacks is used only through its naturality at the inclusion `ℐ ↪ 𝒪`; what
remains is the comparison of the two maps into `𝒪'`, which is
`AlgebraicGeometry.RingedSite.pullbackUnitStructureMap_ringedToposHom`. -/
theorem inverseImageIdealMap_ringedToposHom :
    AlgebraicGeometry.RingedToposHom.inverseImageIdealMap.{u} f.ringedToposHom I =
      (f.pullbackToposIso.app I.toSheafOfModules).hom ≫
        inverseImageIdealMap f I ≫ (toposUnitDiscrepancy f).hom :=
  (congrArg
      (fun m ↦ (f.ringedToposHom.toModulesHom.pullbackModules).map I.ι ≫ m)
      (pullbackUnitStructureMap_ringedToposHom f)).trans
    (((Category.assoc _ _ _).symm.trans
        (congrArg
          (fun m ↦ m ≫ SheafOfModules.pullbackObjUnitToUnit.{u}
              f.toRingedToposSiteHom.fSharpRing ≫ (toposUnitDiscrepancy f).hom)
          (f.pullbackToposIso.hom.naturality I.ι))).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun m ↦ (f.pullbackToposIso.app I.toSheafOfModules).hom ≫ m)
          (Category.assoc _ _ _).symm)))

/-- **The two constructions of `ℐ' = f^{-1}ℐ · 𝒪_X` agree.** For a morphism of ringed sites, the
ideal sheaf of Section 52.7 built over the two-field morphism of ringed topoi of [Stacks, Tag
01D3] part (2) is the one built over the site-presented morphism. No hypothesis on `ℐ`, and none
on `f` beyond its being a morphism of ringed sites.

The canonical map of the topos-level construction is the canonical map of the site-level one
precomposed with an isomorphism and postcomposed with an automorphism of `𝒪'`, by
`AlgebraicGeometry.RingedSite.inverseImageIdealMap_ringedToposHom`, and the image subsheaf is
insensitive to both, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp` and
`.imageSubmodule_comp_unitIso`.

This is what lets the ringed-sites development of [Stacks, Tag 0A0G] and the ringed-topoi one be
used in the same argument: the sheaves of ideals the two sides construct out of the same `ℐ` are
the same sheaf of ideals, so no transport of submodules is needed between them. -/
theorem inverseImageIdealSheaf_ringedToposHom :
    AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf.{u} f.ringedToposHom I =
      inverseImageIdealSheaf f I := by
  refine Eq.trans (congrArg (fun m ↦ Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule m)
    (inverseImageIdealMap_ringedToposHom f I)) ?_
  exact (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp _ _).trans
    (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso _
      (toposUnitDiscrepancy f))

end AlgebraicGeometry.RingedSite

end
