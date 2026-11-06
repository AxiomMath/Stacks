module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The source of 0D35 is quasi-compact and quasi-separated over the base

Let `g : V ⟶ U` be a morphism of algebraic spaces which are the schemes `V₀` and `U₀`, induced by
a surjective étale `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be a morphism of algebraic spaces and let
`pr : Y ⟶ X`, `f' : Y ⟶ V` present `Y` as `V ×_U X`. If some module on `Y` is ample relative to
`f'`, then `f` is quasi-compact and quasi-separated.

This is the first step of the proof of [Stacks, Tag 0D35] (the source opens with "By
Lemma 0D34 the morphism `Y ⟶ V` is quasi-compact and separated, hence so is `X ⟶ U`"): ampleness
relative to `f'` makes `f'` quasi-compact and separated
(`AlgebraicGeometry.Space.IsRelativelyAmple.isQuasiCompact`,
`AlgebraicGeometry.Space.IsRelativelyAmple.isSeparated`), and both properties descend along the
surjective étale chart `yoneda V₀ ⟶ U` of the target, by Stacks 03KG and Stacks 03KM.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_isRelativelyAmple_baseChange_etale` and
  `AlgebraicGeometry.Space.isSeparated_of_isRelativelyAmple_baseChange_etale`: the two
  descents, and `AlgebraicGeometry.Space.isQuasiSeparated_of_isRelativelyAmple_baseChange_etale`.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_relativeAmpleEtaleSourceQcqs
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_relativeAmpleEtaleSourceQcqs
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U V X Y : AlgebraicSpaces B S hS} {f : X ⟶ U} {g : V ⟶ U} {f' : Y ⟶ V} {pr : Y ⟶ X}

/-- The square of 0D35 read on presheaves, with its bottom edge replaced by the chart
`yoneda V₀ ⟶ U` and its right edge by `Y ⟶ yoneda V₀`. -/
theorem isPullback_chart_of_baseChange_etale (hsq : IsPullback pr f' f g)
    {U₀ V₀ : BigFppfOver B S hS} (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀) :
    IsPullback pr.hom (f'.hom ≫ eV.hom) f.hom (yoneda.map h₀ ≫ eU.inv) := by
  have hpre : IsPullback pr.hom f'.hom f.hom g.hom := by
    have hcan := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
    exact IsPullback.of_iso_pullback ⟨congrArg InducedCategory.Hom.hom hsq.w⟩
      ((ObjectProperty.ι _).mapIso (hsq.isoIsPullback _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_fst _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_snd _ _ hcan))
  refine hpre.of_iso (Iso.refl _) (Iso.refl _) eV (Iso.refl _) (by simp) (by simp) (by simp) ?_
  simp only [Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, ← hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (hsq : IsPullback pr f' f g) {U₀ V₀ : BigFppfOver B S hS}
  (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
  (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
  (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
  (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
  {N : Modules.{u, u} B S hS Y.1 Y.2} (hN : IsRelativelyAmple B S hS f' N)

include hsurj in
/-- The chart `yoneda V₀ ⟶ U` is surjective after every represented base change. -/
theorem presheaf_surjective_chart_of_baseChange_etale :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map h₀ ≫ eU.inv) :=
  MorphismProperty.RespectsIso.postcomp _ eU.inv _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ h₀).2 hsurj)

include hetale in
/-- The chart `yoneda V₀ ⟶ U` is étale after every represented base change. -/
theorem presheaf_etale_chart_of_baseChange_etale :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map h₀ ≫ eU.inv) :=
  MorphismProperty.RespectsIso.postcomp _ eU.inv _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ h₀).2 hetale)

/-- The pullback of `f` along the chart `yoneda V₀ ⟶ U` is isomorphic to `Y` over `yoneda V₀`. -/
private theorem exists_iso_pullback_chart_snd (hsq : IsPullback pr f' f g)
    (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀) :
    ∃ he : pullback f.hom (yoneda.map h₀ ≫ eU.inv) ≅ Y.1,
      he.hom ≫ (f'.hom ≫ eV.hom) = pullback.snd f.hom (yoneda.map h₀ ≫ eU.inv) :=
  have hpb := isPullback_chart_of_baseChange_etale hsq eU eV h₀ hg
  ⟨_, (IsPullback.of_hasPullback f.hom _).isoIsPullback_hom_snd _ _ hpb⟩

include hsq hg hsurj hetale hN in
/-- **The source of 0D35 is quasi-compact over the base.** Ampleness relative to `f'` makes `f'`
quasi-compact, and quasi-compactness descends along the surjective étale chart `yoneda V₀ ⟶ U`
(Stacks 03KG). -/
theorem isQuasiCompact_of_isRelativelyAmple_baseChange_etale :
    IsQuasiCompact B S hS f.hom := by
  obtain ⟨he, hsnd⟩ := exists_iso_pullback_chart_snd eU eV h₀ hsq hg
  have hqc : IsQuasiCompact B S hS (f'.hom ≫ eV.hom) :=
    isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := 𝟙 Y.1) (snd := f'.hom ≫ eV.hom) (f := f'.hom)
        (g := eV.inv) ⟨by simp⟩) hN.isQuasiCompact
  refine isQuasiCompact_of_surjectiveEtale_atlas B S hS f.hom X.2 U.2 V₀ _
    (isSurjective_of_presheafSurjective B S hS _
      (presheaf_surjective_chart_of_baseChange_etale eU h₀ hsurj))
    (isEtale_of_presheaf_etale B S hS (presheaf_etale_chart_of_baseChange_etale eU h₀ hetale)) ?_
  rw [← hsnd]
  exact isQuasiCompact_isIso_comp B S hS he.hom hqc

include hsq hg hsurj hetale hN in
/-- **The source of 0D35 is separated over the base.** Ampleness relative to `f'` makes `f'`
separated, and separatedness descends along the surjective étale chart `yoneda V₀ ⟶ U`
(Stacks 03KM). -/
theorem isSeparated_of_isRelativelyAmple_baseChange_etale :
    IsSeparated B S hS f.hom := by
  obtain ⟨he, hsnd⟩ := exists_iso_pullback_chart_snd eU eV h₀ hsq hg
  refine isSeparated_of_etaleChart B S hS X.2
    (presheaf_surjective_chart_of_baseChange_etale eU h₀ hsurj)
    (presheaf_etale_chart_of_baseChange_etale eU h₀ hetale) ?_
  exact (isSeparated_arrow_mk_iso_iff B S hS
    (Arrow.isoMk he.symm eV (by simp [← hsnd]))).1 hN.isSeparated

include hsq hg hsurj hetale hN in
/-- **The source of 0D35 is quasi-separated over the base**, being separated over it. -/
theorem isQuasiSeparated_of_isRelativelyAmple_baseChange_etale :
    IsQuasiSeparated B S hS f.hom :=
  isQuasiSeparated_of_isSeparated B S hS
    (isSeparated_of_isRelativelyAmple_baseChange_etale hsq eU eV h₀ hg hsurj hetale hN)

end AlgebraicGeometry.Space

end
