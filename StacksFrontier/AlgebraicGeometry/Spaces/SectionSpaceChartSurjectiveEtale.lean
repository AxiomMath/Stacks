module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FinalBootstrap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceAlgebraicEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceGeneralCase
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The comparison of spaces of sections along a chart is surjective and étale

Let `Z ⟶ U` be a finite morphism of the big fppf site of `U`, let `w : W ⟶ h_Z` be an étale
morphism of presheaves on that site with `W` an algebraic space, and let `p : h_V ⟶ W` be a
surjective étale chart of `W` whose scheme is separated, with `v = p ≫ w`. The comparison
`AlgebraicGeometry.Space.sectionSpaceMap` of the space of sections of `v` with the space of
sections of `w` is then **surjective and étale**, and with that the general case of Stacks 05XR
follows from the separated case.

The fibre of the comparison over a section `σ` of `W_T ⟶ Z_T` is, by
`AlgebraicGeometry.Space.isPullback_baseChangeSectionPresheaf`, the space of sections of the base
change of `p` along `σ`, and nothing about that space is available directly: the transport of
algebraicity and étaleness to the site over `T` is not established. What is available is the
fibre over a section which *lifts* to the space of sections of `v`: there the fibre is the base
change along the lift of a projection of the kernel pair
`AlgebraicGeometry.Space.isPullback_sectionSpaceMap_self`, and both projections of that kernel
pair are étale and surjective by
`AlgebraicGeometry.Space.isEtale_sectionSpaceMap_pullback_snd` and
`AlgebraicGeometry.Space.isSurjective_sectionSpaceMap_pullback_snd`.

An arbitrary section lifts after a surjective étale cover of its base. That is Stacks 05XQ,
`AlgebraicGeometry.Space.exists_surjective_etale_section_of_isFinite`, applied to the base change
of `p` along `σ` — an algebraic space, surjective and étale over `Z_T = T × Z` — over the base
`T`, along the projection `T × Z ⟶ T`, which is finite because `Z ⟶ U` is
(`AlgebraicGeometry.Space.isFinite_prod_fst`). So the fibre becomes étale after a surjective étale
base change, and étaleness of a morphism of algebraic spaces may be tested on such a base change
by Stacks 03FS condition (3),
`AlgebraicGeometry.Space.isEtale_of_isEtale_pullback_snd`; surjectivity needs no locality, being
cancellation of a surjection on the point sets of Stacks 03BU.

With every fibre of the comparison surjective and étale, the space of sections of `w` is an
algebraic space by Stacks 04S6 condition (5),
`AlgebraicGeometry.Space.isAlgebraicSpace_of_diag_of_flat_chart`, against the two conditions of
Stacks 025Y that hold with no separatedness,
`AlgebraicGeometry.Space.isSheaf_sectionSpace` and
`AlgebraicGeometry.Space.relativelyRepresentable_diag_sectionSpace`. Its structure morphism is
étale because the composite of the chart of the space of sections of `v` with the comparison is a
surjective étale chart of it whose own structure morphism is étale.

## Main results

* `AlgebraicGeometry.Space.isEtale_and_isSurjective_of_isPullback_sectionSpaceMap`: **every fibre
  of the comparison is étale and surjective.**
* `AlgebraicGeometry.Space.isSurjective_sectionSpaceMap_of_chart` and
  `AlgebraicGeometry.Space.isEtale_sectionSpaceMap_of_chart`: **the comparison is surjective and
  étale.**
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_chart` and
  `AlgebraicGeometry.Space.isEtale_sectionSpace_of_chart`: the space of sections of `w` is an
  algebraic space étale over `U`, along a separated surjective étale chart of `W`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isEtale` and
  `AlgebraicGeometry.Space.isEtale_sectionSpace_of_isEtale`: **the general case of Stacks 05XR**,
  the chart being supplied by Stacks 03FX,
  `AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover`.

## Implementation notes

The fibres are taken in the form of an arbitrary cartesian square rather than of the chosen
fibre product, so that the one statement serves both the `CategoryTheory.Limits.pullback.fst`
shape that `AlgebraicGeometry.Space.HasProperty` asks for and the
`CategoryTheory.Limits.pullback.snd` shape that Stacks 03FS condition (3) asks for.

The lift of a section after a surjective étale cover is read off Stacks 05XQ through the
canonical morphism `T' × Z ⟶ T' ×_T (T × Z)` rather than through an isomorphism of those two
objects: only one direction is needed, and the comparison of a product in the site with a
product of representable presheaves is then the one of
`CategoryTheory.Limits.PreservesLimitPair.iso` at the Yoneda embedding.

The finite hypothesis is on the underlying morphism of schemes of `Z ⟶ U`, which is what the
separated case `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated` asks for;
the source states it for a finite locally free `Z ⟶ U`, which is stronger.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The comparison of a product in the site with a product of representables -/

section ProdComparison

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}

/-- The comparison of the Yoneda image of a product of the site with the product of the Yoneda
images is natural in the first factor. -/
private theorem yoneda_prod_map_comm [HasBinaryProducts (BigFppfOver B U hU)]
    {T T' Z : BigFppfOver B U hU} (τ : T' ⟶ T) :
    (PreservesLimitPair.iso yoneda T' Z).inv ≫ yoneda.map (prod.map τ (𝟙 Z)) =
      prod.map (yoneda.map τ) (𝟙 (yoneda.obj Z)) ≫
        (PreservesLimitPair.iso yoneda T Z).inv := by
  rw [Iso.eq_comp_inv]
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
      ← Functor.map_comp, prod.map_fst, Functor.map_comp,
      PreservesLimitPair.iso_inv_fst_assoc, prod.map_fst]
  · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd,
      ← Functor.map_comp, prod.map_snd, Category.comp_id, PreservesLimitPair.iso_inv_snd,
      prod.map_snd, Category.comp_id]

/-- The first projection of a product of the site is finite on underlying schemes as soon as the
structure morphism of the second factor is: it is the first projection of the product of the
representable presheaves, read through the comparison of
`CategoryTheory.Limits.PreservesLimitPair.iso`, and that projection is finite by
`AlgebraicGeometry.Space.isFinite_prod_fst`. -/
private theorem isFinite_toScheme_map_prod_fst [HasBinaryProducts (BigFppfOver B U hU)]
    (T Z : BigFppfOver B U hU)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B U hU).map (prod.fst : T ⨯ Z ⟶ T)) := by
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) := inferInstance
  have hcomm : yoneda.map (prod.fst : T ⨯ Z ⟶ T) =
      (PreservesLimitPair.iso yoneda T Z).hom ≫ prod.fst := by
    rw [← PreservesLimitPair.iso_inv_fst yoneda T Z, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  have hpres := ((isFinite_iff_representable B U hU
    (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)
    (isAlgebraicSpace_yoneda_prod_yoneda T Z) (isAlgebraicSpace_yoneda B U hU T)).1
      (isFinite_prod_fst T Z hZfin)).2
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU))) (PreservesLimitPair.iso yoneda T Z).hom prod.fst hpres
  rw [← hcomm] at hpre
  exact (presheaf_yoneda_map_iff B U hU hPbc (prod.fst : T ⨯ Z ⟶ T)).1 hpre

end ProdComparison

/-! ### The fibres of the comparison along a separated surjective étale chart -/

section SeparatedChart

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z V : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {v : yoneda.obj V ⟶ yoneda.obj Z} {p : yoneda.obj V ⟶ W}

/-- **A section of `W_T ⟶ Z_T` lifts to a section of `V_{T'} ⟶ Z_{T'}` after a surjective étale
cover `T' ⟶ T`.** This is Stacks 05XQ applied to the base change of the chart along the section:
that base change is an algebraic space, surjective and étale over `Z_T = T × Z`, and the
projection `T × Z ⟶ T` is finite because `Z ⟶ U` is. -/
private theorem exists_etale_surjective_cover_lift (hW : IsAlgebraicSpace B U hU W)
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    ∃ (T' : BigFppfOver B U hU) (τ : T' ⟶ T),
      _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B U hU).map τ) ∧
        _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B U hU).map τ) ∧
          ∃ s : SectionsOver B U hU Z T' (yoneda.obj V) v,
            SectionsOver.pushforward hp s = SectionsOver.restrict τ σ := by
  classical
  have : HasBinaryProducts (BigFppfOver B U hU) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  have hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B U hU).map (prod.fst : T ⨯ Z ⟶ T)) :=
    isFinite_toScheme_map_prod_fst T Z hZfin
  have hW' : IsAlgebraicSpace B U hU (pullback σ.1 p) :=
    isAlgebraicSpace_pullback B U hU σ.1 p (isAlgebraicSpace_yoneda_prod_yoneda T Z)
      (isAlgebraicSpace_yoneda B U hU V) hW
  have hw'et : IsEtale B U hU
      (pullback.fst σ.1 p ≫ (PreservesLimitPair.iso yoneda T Z).inv) :=
    isEtale_comp B U hU
      (isEtale_pullback_fst_sectionsOver (isAlgebraicSpace_yoneda B U hU V) hW hpe σ)
      (isEtale_of_isIso B U hU _)
  have hw'surj : IsSurjective B U hU
      (pullback.fst σ.1 p ≫ (PreservesLimitPair.iso yoneda T Z).inv) :=
    isSurjective_comp B U hU
      (isSurjective_pullback_fst_sectionsOver (isAlgebraicSpace_yoneda B U hU V) hW hps σ)
      (pointsMap_surjective_of_isIso B U hU _)
  obtain ⟨T', τ, hτs, hτe, s₀, hs₀⟩ :=
    Space.exists_surjective_etale_section_of_isFinite B U hU (prod.fst : T ⨯ Z ⟶ T)
      (pullback σ.1 p) (pullback.fst σ.1 p ≫ (PreservesLimitPair.iso yoneda T Z).inv) hW'
      hw'surj hw'et
  obtain ⟨c, hcsnd⟩ : ∃ c : T' ⨯ Z ⟶ pullback τ (prod.fst : T ⨯ Z ⟶ T),
      c ≫ pullback.snd τ (prod.fst : T ⨯ Z ⟶ T) = prod.map τ (𝟙 Z) :=
    ⟨pullback.lift (prod.fst : T' ⨯ Z ⟶ T') (prod.map τ (𝟙 Z))
      (prod.map_fst τ (𝟙 Z)).symm, pullback.lift_snd _ _ _⟩
  have hs₀' : s₀ ≫ pullback.fst σ.1 p =
      yoneda.map (pullback.snd τ (prod.fst : T ⨯ Z ⟶ T)) ≫
        (PreservesLimitPair.iso yoneda T Z).hom := by
    rw [← hs₀, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have step1 : s₀ ≫ pullback.snd σ.1 p ≫ p =
      yoneda.map (pullback.snd τ (prod.fst : T ⨯ Z ⟶ T)) ≫
        (PreservesLimitPair.iso yoneda T Z).hom ≫ σ.1 := by
    rw [← pullback.condition, ← Category.assoc, hs₀', Category.assoc]
  have hkey : ((PreservesLimitPair.iso yoneda T' Z).inv ≫
        yoneda.map c ≫ s₀ ≫ pullback.snd σ.1 p) ≫ p =
      prod.map (yoneda.map τ) (𝟙 (yoneda.obj Z)) ≫ σ.1 := by
    have h1 : (PreservesLimitPair.iso yoneda T' Z).inv ≫
        yoneda.map c ≫ s₀ ≫ pullback.snd σ.1 p ≫ p =
          (PreservesLimitPair.iso yoneda T' Z).inv ≫
            yoneda.map (c ≫ pullback.snd τ (prod.fst : T ⨯ Z ⟶ T)) ≫
              (PreservesLimitPair.iso yoneda T Z).hom ≫ σ.1 := by
      rw [Functor.map_comp, step1]
      simp only [Category.assoc]
    simp only [Category.assoc]
    rw [h1, hcsnd, ← Category.assoc, yoneda_prod_map_comm, Category.assoc,
      Iso.inv_hom_id_assoc]
  refine ⟨T', τ, hτs, hτe, ⟨(PreservesLimitPair.iso yoneda T' Z).inv ≫
    yoneda.map c ≫ s₀ ≫ pullback.snd σ.1 p, ?_⟩, Subtype.ext hkey⟩
  rw [← hp, ← Category.assoc, hkey, Category.assoc, σ.2, prod.map_snd, Category.comp_id]

/-- **The fibre of the comparison over a section which lifts to the space of sections of the
chart is étale and surjective.** Such a fibre is a base change of the second projection of the
kernel pair `AlgebraicGeometry.Space.isPullback_sectionSpaceMap_self` along the lift, and that
projection is étale and surjective. -/
private theorem isEtale_and_isSurjective_of_isPullback_of_factors
    (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    {ς : yoneda.obj T ⟶ sectionSpace B U hU Z (yoneda.obj V) v}
    {a : A ⟶ sectionSpace B U hU Z (yoneda.obj V) v} {b : A ⟶ yoneda.obj T}
    (sq : IsPullback a b (sectionSpaceMap hp) (ς ≫ sectionSpaceMap hp)) :
    IsEtale B U hU b ∧ IsSurjective B U hU b := by
  have hv : IsEtale B U hU v := hp ▸ isEtale_comp B U hU hpe hw
  have hX : IsAlgebraicSpace B U hU (sectionSpace B U hU Z (yoneda.obj V) v) :=
    isAlgebraicSpace_sectionSpace_chart hV hv hZfin
  have hK : IsAlgebraicSpace B U hU
      (sectionSpace B U hU Z (pullback p p) (pullback.snd p p ≫ v)) :=
    isAlgebraicSpace_sectionSpace_pullback_chart hW hV hp hpe hw hZfin
  have hsq := IsPullback.of_right' sq (isPullback_sectionSpaceMap_self hp)
  have hb : b = hsq.isoPullback.hom ≫
      pullback.snd (sectionSpaceMap
        (rfl : pullback.snd p p ≫ v = pullback.snd p p ≫ v)) ς :=
    hsq.isoPullback_hom_snd.symm
  refine ⟨?_, ?_⟩
  · rw [hb]
    exact isEtale_comp B U hU (isEtale_of_isIso B U hU _)
      (isEtale_pullback_snd B U hU (isAlgebraicSpace_yoneda B U hU T) hX hK _ ς
        (isEtale_sectionSpaceMap_pullback_snd hW hV hp hpe hw hZfin))
  · rw [hb]
    exact isSurjective_comp B U hU (pointsMap_surjective_of_isIso B U hU _)
      (isSurjective_pullback_snd B U hU hK hX (isAlgebraicSpace_yoneda B U hU T) _ ς
        (isSurjective_sectionSpaceMap_pullback_snd hp))

/-- The point of the space of sections of `w` named by a section `σ` over `T`, restricted along
`τ : T' ⟶ T`, is the comparison applied to the point named by a lift of the restriction. -/
private theorem yoneda_map_comp_sectionPoint (hp : p ≫ w = v)
    {T T' : BigFppfOver B U hU} (τ : T' ⟶ T) (σ : SectionsOver B U hU Z T W w)
    (s : SectionsOver B U hU Z T' (yoneda.obj V) v)
    (hs : SectionsOver.pushforward hp s = SectionsOver.restrict τ σ) :
    yoneda.map τ ≫ yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W w).symm σ) =
      yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T' (yoneda.obj V) v).symm s) ≫
        sectionSpaceMap hp := by
  refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun x => ?_)
  obtain ⟨T''⟩ := T₀
  apply (sectionSpaceEquiv B U hU Z T'' W w).injective
  show sectionSpaceEquiv B U hU Z T'' W w
      ((yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W w).symm σ)).app (op T'')
        ((yoneda.map τ).app (op T'') x)) =
    sectionSpaceEquiv B U hU Z T'' W w ((sectionSpaceMap hp).app (op T'')
      ((yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T' (yoneda.obj V) v).symm s)).app
        (op T'') x))
  rw [sectionSpaceEquiv_yonedaEquiv_symm, sectionSpaceEquiv_sectionSpaceMap,
    sectionSpaceEquiv_yonedaEquiv_symm, ← SectionsOver.restrict_pushforward, hs,
    ← SectionsOver.restrict_comp]
  rfl

/-- **Every fibre of the comparison along a separated surjective étale chart is étale and
surjective.** The section naming the point of the space of sections of `w` lifts to the space of
sections of the chart after a surjective étale cover of its base, by Stacks 05XQ, and over that
cover the fibre is a base change of a projection of the kernel pair, hence étale and surjective.
Étaleness descends along the cover by Stacks 03FS condition (3), and surjectivity by
cancellation on points. -/
theorem isEtale_and_isSurjective_of_isPullback_sectionSpaceMap
    (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    {a : A ⟶ sectionSpace B U hU Z (yoneda.obj V) v} {b : A ⟶ yoneda.obj T}
    {ξ : yoneda.obj T ⟶ sectionSpace B U hU Z W w}
    (sq : IsPullback a b (sectionSpaceMap hp) ξ) :
    IsEtale B U hU b ∧ IsSurjective B U hU b := by
  classical
  set σ := sectionSpaceEquiv B U hU Z T W w (yonedaEquiv ξ) with hσ
  have hξ : ξ = yonedaEquiv.symm ((sectionSpaceEquiv B U hU Z T W w).symm σ) := by
    rw [hσ, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  obtain ⟨T', τ, hτs, hτe, s, hs⟩ :=
    exists_etale_surjective_cover_lift hW hp hpe hps hZfin σ
  have hψe : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU)).presheaf (yoneda.map τ) :=
    (presheaf_yoneda_map_etale_iff B U hU τ).2 hτe
  have hψs : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU)).presheaf (yoneda.map τ) :=
    (presheaf_yoneda_map_iff B U hU
      (P := @_root_.AlgebraicGeometry.Surjective.{u}) inferInstance τ).2 hτs
  have hsq2 : IsPullback (pullback.fst b (yoneda.map τ) ≫ a)
      (pullback.snd b (yoneda.map τ)) (sectionSpaceMap hp) (yoneda.map τ ≫ ξ) :=
    (IsPullback.of_hasPullback b (yoneda.map τ)).paste_horiz sq
  rw [hξ, yoneda_map_comp_sectionPoint hp τ σ s hs] at hsq2
  obtain ⟨hbe, hbs⟩ :=
    isEtale_and_isSurjective_of_isPullback_of_factors hW hV hp hpe hw hZfin hsq2
  refine ⟨isEtale_of_isEtale_pullback_snd B U hU (isAlgebraicSpace_yoneda B U hU T) b
    (yoneda.map τ) hψs hψe hbe, ?_⟩
  have h1 : IsSurjective B U hU (pullback.fst b (yoneda.map τ) ≫ b) := by
    rw [pullback.condition]
    exact isSurjective_comp B U hU hbs (isSurjective_yoneda_map B U hU τ hτs)
  have h2 : Function.Surjective (pointsMap B U hU A b ∘
      pointsMap B U hU (pullback b (yoneda.map τ)) (pullback.fst b (yoneda.map τ))) := by
    rw [← pointsMap_comp]
    exact h1
  exact h2.of_comp

/-! ### The comparison is surjective and étale, and Stacks 05XR along a chart -/

/-- **The comparison of the spaces of sections along a separated surjective étale chart is
surjective.** Every represented base change of it is surjective, which is surjectivity by
Stacks 03MF. -/
theorem isSurjective_sectionSpaceMap_of_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsSurjective B U hU (sectionSpaceMap hp) :=
  isSurjective_of_isSurjective_affine_baseChange B U hU (sectionSpaceMap hp) fun _ _ g =>
    (isEtale_and_isSurjective_of_isPullback_sectionSpaceMap hW hV hp hpe hps hw hZfin
      (IsPullback.of_hasPullback (sectionSpaceMap hp) g)).2

/-- **The space of sections of `w` is an algebraic space, along a separated surjective étale
chart of `W`.** It is an fppf sheaf with representable absolute diagonal by the two conditions of
Stacks 025Y which hold with no separatedness, and the comparison with the space of sections of
the chart is a surjective étale chart of it by
`AlgebraicGeometry.Space.isEtale_and_isSurjective_of_isPullback_sectionSpaceMap`, so Stacks 03Y3
conditions (1), (2) and (3) apply. Along an étale chart no clause of Stacks 04S6 is needed. -/
theorem isAlgebraicSpace_sectionSpace_of_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) := by
  have hv : IsEtale B U hU v := hp ▸ isEtale_comp B U hU hpe hw
  have key : ∀ (T : BigFppfOver B U hU) (ξ : yoneda.obj T ⟶ sectionSpace B U hU Z W w),
      IsEtale B U hU (pullback.fst ξ (sectionSpaceMap hp)) ∧
        IsSurjective B U hU (pullback.fst ξ (sectionSpaceMap hp)) := fun _ ξ =>
    isEtale_and_isSurjective_of_isPullback_sectionSpaceMap hW hV hp hpe hps hw hZfin
      (IsPullback.of_hasPullback ξ (sectionSpaceMap hp)).flip
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_diag
    (isSheaf_sectionSpace hW hw hZfin)
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable
      (relativelyRepresentable_diag_sectionSpace hW hw hZfin))
    (isAlgebraicSpace_sectionSpace_chart hV hv hZfin) (sectionSpaceMap hp)
    (fun T ξ => (key T ξ).2)
    (fun T ξ => (key T ξ).1)

/-- **The comparison of the spaces of sections along a separated surjective étale chart is
étale.** Its base change along a surjective étale chart of the space of sections of `w` — which
is an algebraic space by
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_chart` — is étale, so Stacks 03FS
condition (3) applies. -/
theorem isEtale_sectionSpaceMap_of_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (sectionSpaceMap hp) := by
  have hF := isAlgebraicSpace_sectionSpace_of_chart hW hV hp hpe hps hw hZfin
  obtain ⟨T, ψ, hψs, hψe⟩ := hF.exists_atlas
  exact isEtale_of_isEtale_pullback_snd B U hU hF (sectionSpaceMap hp) ψ hψs hψe
    (isEtale_and_isSurjective_of_isPullback_sectionSpaceMap hW hV hp hpe hps hw hZfin
      (IsPullback.of_hasPullback (sectionSpaceMap hp) ψ)).1

/-- **The space of sections of `w` is étale over `U`, along a separated surjective étale chart of
`W`.** A scheme atlas of the space of sections of the chart, composed with the comparison, is a
surjective étale chart of the space of sections of `w`, and its structure morphism is étale
because the space of sections of the chart is étale over `U`; Stacks 03FS condition (2) then
applies. -/
theorem isEtale_sectionSpace_of_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hps : IsSurjective B U hU p)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (terminal.from (sectionSpace B U hU Z W w)) := by
  have hv : IsEtale B U hU v := hp ▸ isEtale_comp B U hU hpe hw
  have hF := isAlgebraicSpace_sectionSpace_of_chart hW hV hp hpe hps hw hZfin
  obtain ⟨V', q, hqs, hqe⟩ := (isAlgebraicSpace_sectionSpace_chart hV hv hZfin).exists_atlas
  refine (isEtale_iff_exists_source_chart B U hU hF (isAlgebraicSpace_terminal B U hU) _).2
    ⟨V', q ≫ sectionSpaceMap hp, ?_,
      isEtale_sectionSpaceMap_of_chart hW hV hp hpe hps hw hZfin V' q hqe, ?_⟩
  · exact (presheafSurjective_iff_isSurjective_yoneda B U hU _ hF V' _).2
      (isSurjective_comp B U hU (isSurjective_of_presheafSurjective B U hU q hqs)
        (isSurjective_sectionSpaceMap_of_chart hW hV hp hpe hps hw hZfin))
  · rw [show (q ≫ sectionSpaceMap hp) ≫ terminal.from (sectionSpace B U hU Z W w) =
        q ≫ terminal.from (sectionSpace B U hU Z (yoneda.obj V) v) from terminal.hom_ext _ _]
    exact isEtale_comp B U hU ((isEtale_iff_presheaf_of_yoneda B U hU q).2 hqe)
      (isEtale_sectionSpace_chart hV hv hZfin)

end SeparatedChart

/-! ### The general case of Stacks 05XR -/

section General

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {w : W ⟶ yoneda.obj Z}

/-- A separated surjective étale chart of an algebraic space, in the form used for the
comparison of the spaces of sections. -/
private theorem exists_separated_etale_surjective_chart (hW : IsAlgebraicSpace B U hU W) :
    ∃ (V : BigFppfOver B U hU) (p : yoneda.obj V ⟶ W),
      Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V) ∧ IsEtale B U hU p ∧
        IsSurjective B U hU p := by
  obtain ⟨V, p, hVsep, hps, hpe⟩ :=
    _root_.AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover
      B U hU W hW
  exact ⟨V, p, hVsep, (isEtale_iff_presheaf_of_yoneda B U hU p).2 hpe,
    isSurjective_of_presheafSurjective B U hU p hps⟩

/-- **Stacks 05XR, the algebraicity of the space of sections, in general.** Let `Z ⟶ U` be a
morphism of the big fppf site of `U` whose underlying morphism of schemes is finite, and let
`w : W ⟶ h_Z` be an étale morphism of presheaves with `W` an algebraic space over `U`. Then the
space of sections of `W_T ⟶ Z_T` is an algebraic space over `U`.

No separatedness is assumed: a surjective étale chart of `W` whose scheme is separated exists by
Stacks 03FX, and along such a chart the comparison of the spaces of sections is surjective and
étale by `AlgebraicGeometry.Space.isEtale_and_isSurjective_of_isPullback_sectionSpaceMap`. -/
@[stacks 05XR "the space of sections is an algebraic space, with no separatedness"]
theorem isAlgebraicSpace_sectionSpace_of_isEtale (hW : IsAlgebraicSpace B U hU W)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) := by
  obtain ⟨V, p, hVsep, hpe, hps⟩ := exists_separated_etale_surjective_chart hW
  exact isAlgebraicSpace_sectionSpace_of_chart hW hVsep rfl hpe hps hw hZfin

/-- **Stacks 05XR, the étaleness of the space of sections over the base, in general.** Under the
hypotheses of `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isEtale` the structure
morphism of the space of sections to `U` is étale. -/
@[stacks 05XR "the space of sections is étale over the base, with no separatedness"]
theorem isEtale_sectionSpace_of_isEtale (hW : IsAlgebraicSpace B U hU W)
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (terminal.from (sectionSpace B U hU Z W w)) := by
  obtain ⟨V, p, hVsep, hpe, hps⟩ := exists_separated_etale_surjective_chart hW
  exact isEtale_sectionSpace_of_chart hW hVsep rfl hpe hps hw hZfin

end General

end AlgebraicGeometry.Space

end
