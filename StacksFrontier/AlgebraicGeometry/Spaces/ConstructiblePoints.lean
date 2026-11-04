module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Constructible
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Constructible.Homeomorph

/-!
# Étale-locally constructible subsets of an algebraic space

A subset of the points of an algebraic space over `S` is *étale locally constructible* when
its inverse image on every étale scheme chart is locally constructible. That condition can
equivalently be tested on affine étale charts, where it becomes constructibility, or on a
single surjective étale chart.

Both comparisons rest on clause (1) of Tag 03BX: the point space of a represented presheaf is
homeomorphic to the representing scheme, so the conditions are statements about subsets of
schemes. The affine comparison is then the corresponding statement for schemes, Tag 054C,
together with the fact that an affine open of an object of the site is again an object of the
site; the one-chart comparison is descent of local constructibility along a surjective étale
morphism of schemes, applied to a chart of the fibre product of the two charts.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleLocallyConstructible` is **Stacks 0ECU**.

## Main results

* `AlgebraicGeometry.Space.forall_etale_iff_forall_affine_etale` and
  `AlgebraicGeometry.Space.forall_etale_iff_exists_surjective_etale` are the two comparisons
  of **Stacks 0ECT**.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here. The definition of Tag 0ECU is condition (1) of Tag 0ECT, so the
two comparisons are stated with it on the left-hand side.

## References

* [Stacks Project, Tag 0ECT](https://stacks.math.columbia.edu/tag/0ECT)
* [Stacks Project, Tag 0ECU](https://stacks.math.columbia.edu/tag/0ECU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology
open scoped Set.Notation

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Naturality of the identification of the points of a represented presheaf with the points
of the representing scheme, read through the inverse homeomorphism. -/
theorem schemePointsHomeomorph_symm_naturality {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map g)
        ((schemePointsHomeomorph B S hS U).symm x) =
      (schemePointsHomeomorph B S hS V).symm ((BigFppfOver.toScheme B S hS).map g x) := by
  apply (schemePointsHomeomorph B S hS V).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
    pointsToScheme_pointsMap, ← schemePointsHomeomorph_apply,
    Homeomorph.apply_symm_apply]

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (E : Set (points B S hS X))

/-- The preimage of a set of points of `X` under a morphism of charts, read in the schemes. -/
private theorem preimage_toScheme_map_preimage_symm {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (f : yoneda.obj V ⟶ X) :
    ((BigFppfOver.toScheme B S hS).map g) ⁻¹'
        ((schemePointsHomeomorph B S hS V).symm ⁻¹'
          (pointsMap B S hS (yoneda.obj V) f ⁻¹' E)) =
      (schemePointsHomeomorph B S hS U).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj U) (yoneda.map g ≫ f) ⁻¹' E) := by
  ext x
  show pointsMap B S hS (yoneda.obj V) f ((schemePointsHomeomorph B S hS V).symm
      ((BigFppfOver.toScheme B S hS).map g x)) ∈ E ↔ _
  rw [← schemePointsHomeomorph_symm_naturality, ← pointsMap_comp_apply]
  rfl

/-- **Stacks 0ECU.** A subset of the points of a presheaf on the big fppf site of `S` is
*étale locally constructible* when its inverse image on every étale chart from a scheme is a
locally constructible subset of that chart. -/
@[stacks 0ECU]
abbrev IsEtaleLocallyConstructible : Prop :=
  ∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X), IsEtale B S hS f →
    IsLocallyConstructible (pointsMap B S hS (yoneda.obj U) f ⁻¹' E)

/-- **Stacks 0ECT, conditions (1) and (2).** Étale-local constructibility can be tested on
affine étale charts, where it becomes constructibility. -/
@[stacks 0ECT "conditions (1) and (2)"]
theorem forall_etale_iff_forall_affine_etale :
    IsEtaleLocallyConstructible B S hS X E ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (f : yoneda.obj U ⟶ X), IsEtale B S hS f →
          IsConstructible (pointsMap B S hS (yoneda.obj U) f ⁻¹' E) := by
  constructor
  · intro h U hU f hf
    refine ((schemePointsHomeomorph B S hS U).symm.isConstructible_preimage_iff _).mp ?_
    exact (((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff
      _).mpr (h U f hf)).isConstructible
  · intro h U f hf
    refine ((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff
      _).mp ?_
    refine (isLocallyConstructible_iff_forall_affineOpens _).2 fun V ↦ ?_
    -- An affine open of the chart is itself an affine étale chart.
    let W := openSiteObject B S hS U V.1
    let i := openSiteObjectHom B S hS U V.1
    have hiMap : (BigFppfOver.toScheme B S hS).map i = V.1.ι := map_openSiteObjectHom B S hS U V.1
    have hiScheme : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map i) :=
      hiMap ▸ AlgebraicGeometry.Etale.instOfIsOpenImmersion V.1.ι
    have hi : IsEtale B S hS (yoneda.map i) :=
      isEtale_of_presheaf_etale B S hS ((presheaf_yoneda_map_etale_iff B S hS i).2 hiScheme)
    have hCW := h W V.2 (yoneda.map i ≫ f) (isEtale_comp B S hS hi hf)
    have hsets : (schemePointsHomeomorph B S hS W).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj W) (yoneda.map i ≫ f) ⁻¹' E) =
          (V.1 : Set ((BigFppfOver.toScheme B S hS).obj U)) ↓∩
            ((schemePointsHomeomorph B S hS U).symm ⁻¹'
              (pointsMap B S hS (yoneda.obj U) f ⁻¹' E)) := by
      rw [← preimage_toScheme_map_preimage_symm B S hS X E i f, hiMap]
      rfl
    rw [← hsets]
    exact ((schemePointsHomeomorph B S hS W).symm.isConstructible_preimage_iff _).mpr hCW

/-- **Stacks 0ECT, conditions (1) and (3).** Étale-local constructibility holds as soon as it
holds on a single surjective étale chart. -/
@[stacks 0ECT "conditions (1) and (3)"]
theorem forall_etale_iff_exists_surjective_etale (hX : IsAlgebraicSpace B S hS X) :
    IsEtaleLocallyConstructible B S hS X E ↔
      ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
        IsSurjective B S hS f ∧ IsEtale B S hS f ∧
          IsLocallyConstructible (pointsMap B S hS (yoneda.obj U) f ⁻¹' E) := by
  constructor
  · intro hall
    obtain ⟨U, f, hfs, hfe⟩ := hX.exists_atlas
    have hfEt : IsEtale B S hS f := isEtale_of_presheaf_etale B S hS hfe
    exact ⟨U, f, (surjective_iff_surjective_pointsMap B S hS X hX U f).mp hfs, hfEt,
      hall U f hfEt⟩
  · rintro ⟨U₀, f₀, hf₀s, hf₀e, hf₀lc⟩ U f hf
    -- The fibre product of the two charts has a scheme chart, surjective and étale over `U`.
    let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let U₀sp : AlgebraicSpaces B S hS := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩
    let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
    let f₀sp : U₀sp ⟶ Xsp := ObjectProperty.homMk f₀
    let fsp : Usp ⟶ Xsp := ObjectProperty.homMk f
    let W := AlgebraicSpaces.fiberProduct B S hS f₀sp fsp
    let p₀ : W ⟶ U₀sp := ObjectProperty.homMk (pullback.fst f₀ f)
    let p₁ : W ⟶ Usp := ObjectProperty.homMk (pullback.snd f₀ f)
    have sq : IsPullback p₀ p₁ f₀sp fsp := AlgebraicSpaces.isPullback_fiberProduct B S hS f₀sp fsp
    have hp₁e : IsEtale B S hS p₁.hom :=
      isEtale_of_isPullback B S hS p₀ p₁ f₀sp fsp sq hf₀e
    have hp₁s : IsSurjective B S hS p₁.hom := isSurjective_of_isPullback B S hS sq hf₀s
    obtain ⟨T, t, hts, hte⟩ := W.property.exists_atlas
    have htPts : IsSurjective B S hS t :=
      (surjective_iff_surjective_pointsMap B S hS W.1 W.property T t).mp hts
    have htRel : IsEtale B S hS t := isEtale_of_presheaf_etale B S hS hte
    let q₀ : T ⟶ U₀ := yonedaEquiv (t ≫ p₀.hom)
    let q₁ : T ⟶ U := yonedaEquiv (t ≫ p₁.hom)
    have hq₀map : yoneda.map q₀ = t ≫ p₀.hom := by
      apply yonedaEquiv.injective; rw [yonedaEquiv_yoneda_map]
    have hq₁map : yoneda.map q₁ = t ≫ p₁.hom := by
      apply yonedaEquiv.injective; rw [yonedaEquiv_yoneda_map]
    have hq₁Pts : Function.Surjective
        (pointsMap B S hS (yoneda.obj T) (yoneda.map q₁)) := by
      rw [hq₁map]
      exact isSurjective_comp B S hS htPts hp₁s
    have hq₁surj : Function.Surjective ((BigFppfOver.toScheme B S hS).map q₁) := by
      refine fun y ↦ ?_
      obtain ⟨x, hx⟩ := hq₁Pts ((schemePointsHomeomorph B S hS U).symm y)
      refine ⟨schemePointsHomeomorph B S hS T x, ?_⟩
      apply (schemePointsHomeomorph B S hS U).symm.injective
      rw [← hx, ← schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply]
    have hq₁rel : IsEtale B S hS (yoneda.map q₁) := by
      rw [hq₁map]; exact isEtale_comp B S hS htRel hp₁e
    have hq₁e : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q₁) :=
      (presheaf_yoneda_map_etale_iff B S hS q₁).1
        ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q₁)).1 hq₁rel)
    -- The two charts agree over the algebraic space, so the two preimages agree on `T`.
    have hsqhom : p₀.hom ≫ f₀ = p₁.hom ≫ f := by
      show (p₀ ≫ f₀sp).hom = (p₁ ≫ fsp).hom
      rw [sq.w]
    have hcomm : yoneda.map q₀ ≫ f₀ = yoneda.map q₁ ≫ f := by
      rw [hq₀map, hq₁map, Category.assoc, Category.assoc, hsqhom]
    have hsets :
        ((BigFppfOver.toScheme B S hS).map q₁) ⁻¹'
            ((schemePointsHomeomorph B S hS U).symm ⁻¹'
              (pointsMap B S hS (yoneda.obj U) f ⁻¹' E)) =
          ((BigFppfOver.toScheme B S hS).map q₀) ⁻¹'
            ((schemePointsHomeomorph B S hS U₀).symm ⁻¹'
              (pointsMap B S hS (yoneda.obj U₀) f₀ ⁻¹' E)) := by
      rw [preimage_toScheme_map_preimage_symm, preimage_toScheme_map_preimage_symm, hcomm]
    refine ((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff
      _).mp ?_
    refine isLocallyConstructible_of_etale_surjective
      ((BigFppfOver.toScheme B S hS).map q₁) hq₁e hq₁surj ?_
    rw [hsets]
    exact isLocallyConstructible_preimage _
      (((schemePointsHomeomorph B S hS U₀).symm.isLocallyConstructible_preimage_iff _).mpr
        hf₀lc)

end AlgebraicGeometry.Space

end
