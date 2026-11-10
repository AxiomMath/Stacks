module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLiftsFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NoetherianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessinger
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport
public import StacksFrontier.Deformation.Examples.Spaces
public import StacksFrontier.Deformation.Terminal

/-!
# Deformations of an algebraic space satisfy the Rim-Schlessinger condition (Stacks 0E40)

Let `A₁ ⟶ A` and `A₂ ⟶ A` be morphisms of `𝒞_Λ` with `A₂ ⟶ A` surjective. The square of
spectra of `A`, `A₁`, `A₂` and of the fibre product `A₁ ×_A A₂` is a pushout of algebraic spaces
along the thickening `Spec A ⟶ Spec A₂` and the affine morphism `Spec A ⟶ Spec A₁`
([Stacks Project, Tag 07SY]). A pair of flat families over `A₁` and `A₂` restricting to a common
family over `A` is glued to the pushout of algebraic spaces of [Stacks Project, Tag 07VX]; that
pushout is flat over the spectrum of the fibre product and restricts to the two given families
([Stacks Project, Tag 07W3], clause (2), and [Stacks Project, Tag 07W0]), and conversely a flat
family over the fibre product is the pushout of its two restrictions (the counit assertion of
[Stacks Project, Tag 07W3]). Together these give condition (RS) for the category of flat families
of algebraic spaces of [Stacks Project, Tag 0E3Z], which is [Stacks Project, Tag 0E40]; its
in-particular clause, that the deformation category of a fixed algebraic space over `k` is a
deformation category, follows because that category lies over the residue field, a terminal
object of `𝒞_Λ`.

## Main results

* `Deformation.Examples.satisfiesRS_flatAlgebraicSpaceFamilyFunctor`: **Stacks 0E40**, the
  category of flat families of algebraic spaces satisfies condition (RS).
* `Deformation.Examples.isDeformationCategory_spaceDeformationProjection`: **Stacks 0E40**, the
  deformation category of an algebraic space over `k` is a deformation category.

## Implementation notes

The proof follows that of the scheme case, Stacks 0DY8
(`Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection`), in the category
`AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `Spec Λ`. The gluing inputs are the
chart presentations of a pushout of algebraic spaces along a thickening and an affine morphism:
`AlgebraicGeometry.Space.exists_thickeningAffineGluingChart_of_isFiniteOrderThickening` supplies,
for the glued space, the cartesian squares (`ThickeningAffineGluingChart.isPullback_v` and
`ThickeningAffineGluingChart.isPullback_u'`) and flatness
(`ThickeningAffineGluingChart.isFlat_iff`), and
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas` is the descent of a flat
space over the pushout. These consume the lifting of étale charts across the thickening
`Spec A ⟶ Spec A₂` and its base changes, which have finite order because `A₂` is Noetherian
(`AlgebraicGeometry.Space.isFiniteOrderThickening_of_atlas`); the lifting is
`AlgebraicGeometry.Space.exists_etaleChart_lift_of_isFiniteOrderThickening`.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 0E40](https://stacks.math.columbia.edu/tag/0E40)
* [Stacks Project, Tag 06J5](https://stacks.math.columbia.edu/tag/06J5)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Space CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

open Deformation.ArtinianLocalAlgCat

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-- The morphism of spectra over `Spec Λ` induced by a morphism of `𝒞_Λ` is, as a morphism of
schemes, the map of spectra of the underlying ring map. -/
theorem toScheme_map_spaceBaseOverMap {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ A') :
    (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceBaseOverMap B hΛ hSpec f) =
      baseSpecMap f :=
  B.inclusion.map_preimage _

/-- The spectrum of an object of `𝒞_Λ`, as an object of the big fppf site, is affine. -/
theorem isAffine_toScheme_spaceBaseOver (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj (spaceBaseOver B hΛ hSpec A)) := by
  change IsAffine (Spec (.of A))
  infer_instance

/-- A surjection of `𝒞_Λ` induces a thickening of algebraic spaces on spectra. -/
theorem isThickeningHom_schemeSpaceMap_spaceBaseOverMap
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ A') (hf : Function.Surjective f.hom) :
    IsThickeningHom B (Spec (.of Λ)) hΛ (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f)) := by
  have ht := (isFiniteOrderThickening_baseSpecMap f hf).isThickening
  rw [← toScheme_map_spaceBaseOverMap B hΛ hSpec f] at ht
  have : Surjective ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceBaseOverMap B hΛ hSpec f)) := ⟨ht.2⟩
  refine (isThickeningHom_iff_isClosedImmersion_and_isSurjective B (Spec (.of Λ)) hΛ _).2
    ⟨?_, ?_⟩
  · exact (presheaf_yoneda_map_iff B (Spec (.of Λ)) hΛ
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance _).2 ht.1
  · exact isSurjective_yoneda_map B (Spec (.of Λ)) hΛ _ this

/-- A morphism of `𝒞_Λ` induces an affine morphism of algebraic spaces on spectra. -/
theorem isAffineHom_schemeSpaceMap_spaceBaseOverMap
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ A') :
    IsAffineHom B (Spec (.of Λ)) hΛ (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f)).hom := by
  have := isAffine_toScheme_spaceBaseOver B hΛ hSpec A
  have := isAffine_toScheme_spaceBaseOver B hΛ hSpec A'
  exact isAffineHom_yoneda_map B (Spec (.of Λ)) hΛ _

/-- **The pushout of spectra, for algebraic spaces.** For a cospan of `𝒞_Λ` whose second leg is
surjective, the spectrum of the fibre product is the pushout, in the category of algebraic
spaces over `Spec Λ`, of the two spectra along the spectrum of the common target. This is
[Stacks Project, Tag 07SY] applied to the pushout of schemes of [Stacks Project, Tag 0ET0]. -/
theorem isPushout_schemeSpaceMap_spaceBaseOverMap {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) (h₂ : Function.Surjective f₂.hom) :
    IsPushout (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f₂))
      (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f₁))
      (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec (pullbackSnd_of_surjective f₁ f₂ (Or.inr h₂))))
      (schemeSpaceMap (spaceBaseOverMap B hΛ hSpec
        (pullbackFst_of_surjective f₁ f₂ (Or.inr h₂)))) := by
  have ht := (isFiniteOrderThickening_baseSpecMap f₂ h₂).isThickening
  rw [← toScheme_map_spaceBaseOverMap B hΛ hSpec f₂] at ht
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceBaseOverMap B hΛ hSpec f₁)) := by
    have := isAffine_toScheme_spaceBaseOver B hΛ hSpec A
    have := isAffine_toScheme_spaceBaseOver B hΛ hSpec A₁
    infer_instance
  have hpo := isPushout_baseSpecMap_of_surjective f₁ f₂ h₂
  rw [← toScheme_map_spaceBaseOverMap B hΛ hSpec f₂, ← toScheme_map_spaceBaseOverMap B hΛ hSpec f₁,
    ← toScheme_map_spaceBaseOverMap B hΛ hSpec, ← toScheme_map_spaceBaseOverMap B hΛ hSpec] at hpo
  exact isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B (Spec (.of Λ)) hΛ _ _ _ _
    ht hpo

/-- **Stacks Project, Tag 0E40.** The category of flat families of algebraic spaces over `𝒞_Λ` of
Example 0E3Z satisfies the Rim-Schlessinger condition (RS).

For a cospan `X₁ ⟶ X ⟵ X₂` of flat families over `A₁ ⟶ A ⟵ A₂` with `A₂ ⟶ A` surjective, the
pushout of algebraic spaces `X₂ ⨿_X X₁` (Stacks 07VX), with its morphism to the spectrum of
`A₁ ×_A A₂`, is a flat family (Stacks 07W3, clause (2)) restricting to `X₁` and `X₂` (Stacks
07W0); it is a fibre product of flat families because any flat family over `A₁ ×_A A₂` is the
pushout of its two restrictions (the counit assertion of Stacks 07W3). -/
@[stacks 0E40 "condition (RS) for the category of flat families of algebraic spaces of \
Example 0E3Z"]
theorem satisfiesRS_flatAlgebraicSpaceFamilyFunctor :
    SatisfiesRS (flatAlgebraicSpaceFamilyFunctor B hΛ hSpec) := by
  classical
  refine ⟨flatAlgebraicSpaceFamilyFunctor_isCofiberedInGroupoids B hΛ hSpec, ?_⟩
  intro X₁ X₂ X f₁ f₂ h₂
  have hsurj : Function.Surjective f₂.base.hom := h₂
  let hor : Function.Surjective f₁.base.hom ∨ Function.Surjective f₂.base.hom := Or.inr hsurj
  let P : ArtinianLocalAlgCat.{u, u, u} Λ k := pullbackObj_of_surjective f₁.base f₂.base hor
  let q₁ : P ⟶ X₁.base := pullbackFst_of_surjective f₁.base f₂.base hor
  let q₂ : P ⟶ X₂.base := pullbackSnd_of_surjective f₁.base f₂.base hor
  have hbp : IsPullback q₁ q₂ f₁.base f₂.base := isPullback_of_surjective _ _ hor
  -- the spectra, as algebraic spaces over `Spec Λ`
  let i := schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f₂.base)
  let fb := schemeSpaceMap (spaceBaseOverMap B hΛ hSpec f₁.base)
  let aY := schemeSpaceMap (spaceBaseOverMap B hΛ hSpec q₂)
  let bY := schemeSpaceMap (spaceBaseOverMap B hΛ hSpec q₁)
  have hi : IsThickeningHom B (Spec (.of Λ)) hΛ i :=
    isThickeningHom_schemeSpaceMap_spaceBaseOverMap B hΛ hSpec f₂.base hsurj
  have hf : IsAffineHom B (Spec (.of Λ)) hΛ fb.hom :=
    isAffineHom_schemeSpaceMap_spaceBaseOverMap B hΛ hSpec f₁.base
  have hE : IsPushout i fb aY bY :=
    isPushout_schemeSpaceMap_spaceBaseOverMap B hΛ hSpec f₁.base f₂.base hsurj
  -- the three families, as algebraic spaces over `Spec Λ`
  let sX : FlatAlgebraicSpaceFamily B hΛ hSpec → AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
    fun Q => ⟨Q.space, Q.algebraic⟩
  let j₂ : sX X ⟶ sX X₂ := ObjectProperty.homMk f₂.map
  let j₁ : sX X ⟶ sX X₁ := ObjectProperty.homMk f₁.map
  let pX : sX X ⟶ schemeSpace (spaceBaseOver B hΛ hSpec X.base) := ObjectProperty.homMk X.toBase
  let u' : sX X₂ ⟶ schemeSpace (spaceBaseOver B hΛ hSpec X₂.base) :=
    ObjectProperty.homMk X₂.toBase
  let v : sX X₁ ⟶ schemeSpace (spaceBaseOver B hΛ hSpec X₁.base) :=
    ObjectProperty.homMk X₁.toBase
  have hU' : IsPullback j₂ pX u' i :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) f₂.cartesian
  have hV : IsPullback j₁ pX v fb :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) f₁.cartesian
  have hj₂ : IsThickeningHom B (Spec (.of Λ)) hΛ j₂ :=
    isThickeningHom_of_isPullback B (Spec (.of Λ)) hΛ hU'.flip hi
  have hj₁ : IsAffineHom B (Spec (.of Λ)) hΛ j₁.hom :=
    IsAffineHom.of_isPullback f₁.cartesian.flip hf
  -- the thickening of spectra has finite order, the spectrum of `A₂` being Noetherian
  have hin : IsFiniteOrderThickening B (Spec (.of Λ)) hΛ
      (schemeSpace (spaceBaseOver B hΛ hSpec X₂.base)) (Subfunctor.range i.hom) := by
    have : IsNoetherian ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
        (spaceBaseOver B hΛ hSpec X₂.base)) := by
      change IsNoetherian (Spec (.of X₂.base))
      infer_instance
    refine isFiniteOrderThickening_of_atlas B (Spec (.of Λ)) hΛ hi.2
      (spaceBaseOver B hΛ hSpec X₂.base) (yoneda.map (𝟙 _)) ?_ ?_
    · exact (presheaf_yoneda_map_iff B (Spec (.of Λ)) hΛ
        (P := @AlgebraicGeometry.Surjective.{u}) inferInstance _).2
        (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    · exact (presheaf_yoneda_map_iff B (Spec (.of Λ)) hΛ
        (P := @AlgebraicGeometry.Etale.{u}) inferInstance _).2
        (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hj₂n : IsFiniteOrderThickening B (Spec (.of Λ)) hΛ (sX X₂) (Subfunctor.range j₂.hom) :=
    isFiniteOrderThickening_range_of_isPullback B (Spec (.of Λ)) hΛ hU'.flip hin
  -- the glued algebraic space
  obtain ⟨A₂⟩ := nonempty_thickeningAffineAtlas_of_chartLift B (Spec (.of Λ)) hΛ j₂ j₁ hj₂ hj₁
    (exists_etaleChart_lift_of_isFiniteOrderThickening B (Spec (.of Λ)) hΛ j₂ hj₂ hj₂n)
  have : HasPushout j₂ j₁ := by
    obtain ⟨_, _, _, hpo, -⟩ := isPushout_quotient_of_thickeningAffineAtlas B (Spec (.of Λ)) hΛ A₂
    exact hpo.hasPushout
  have hZpo : IsPushout j₂ j₁ (pushout.inl j₂ j₁) (pushout.inr j₂ j₁) :=
    IsPushout.of_hasPushout _ _
  set c₂ := pushout.inl j₂ j₁ with hc₂def
  set c₁ := pushout.inr j₂ j₁ with hc₁def
  have hzw : j₂ ≫ u' ≫ aY = j₁ ≫ v ≫ bY := by
    rw [← Category.assoc, ← Category.assoc, hU'.w, hV.w, Category.assoc, Category.assoc, hE.w]
  set g := hZpo.desc (u' ≫ aY) (v ≫ bY) hzw with hgdef
  have hgc₂ : c₂ ≫ g = u' ≫ aY := hZpo.inl_desc _ _ _
  have hgc₁ : c₁ ≫ g = v ≫ bY := hZpo.inr_desc _ _ _
  obtain ⟨D, hDV, hDU, hDY, hDX⟩ := exists_thickeningAffineGluingChart_of_isFiniteOrderThickening
    B (Spec (.of Λ)) hΛ hi hin hf hE hU' hV hZpo hgc₂ hgc₁
  have hc₁ : IsPullback c₁.hom X₁.toBase g.hom (yoneda.map (spaceBaseOverMap B hΛ hSpec q₁)) :=
    (D.isPullback_v hgc₁ hDV hDY).flip
  have hc₂ : IsPullback c₂.hom X₂.toBase g.hom (yoneda.map (spaceBaseOverMap B hΛ hSpec q₂)) :=
    (D.isPullback_u' hgc₂ hDU hDX).flip
  have hzflat : Space.IsFlat B (Spec (.of Λ)) hΛ g.hom := D.isFlat_iff.2 ⟨X₁.flat, X₂.flat⟩
  let ZF : FlatAlgebraicSpaceFamily B hΛ hSpec :=
    { base := P
      space := (pushout j₂ j₁).1
      algebraic := (pushout j₂ j₁).2
      toBase := g.hom
      flat := hzflat }
  let a₁ : ZF ⟶ X₁ := { base := q₁, map := c₁.hom, cartesian := hc₁ }
  let a₂ : ZF ⟶ X₂ := { base := q₂, map := c₂.hom, cartesian := hc₂ }
  have hw : a₁ ≫ f₁ = a₂ ≫ f₂ :=
    FlatAlgebraicSpaceFamily.Hom.ext hbp.w (congrArg (fun φ => φ.hom) hZpo.w).symm
  -- the chart of the pushout of spectra, for the descent of flat families
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_chartLift B (Spec (.of Λ)) hΛ i fb hi hf
    (exists_etaleChart_lift_of_isFiniteOrderThickening B (Spec (.of Λ)) hΛ i hi hin)
  obtain ⟨Epo, aY₀, bY₀, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B (Spec (.of Λ)) hΛ A hi
  let eP : Epo.1 ≅ (schemeSpace (spaceBaseOver B hΛ hSpec P)).1 :=
    (ObjectProperty.ι _).mapIso (hpush.isoIsPushout _ _ hE)
  have hinl : aY₀.hom ≫ eP.hom = aY.hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have hinr : bY₀.hom ≫ eP.hom = bY.hom :=
    congrArg (fun φ => φ.hom) (hpush.inr_isoIsPushout_hom _ _ hE)
  have hqm' : IsPullback (yoneda.map A.s) (yoneda.map A.t) (qm ≫ eP.hom) (qm ≫ eP.hom) :=
    hqm.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simp)
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom) aY.hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinl)
  have hbY'' : IsPullback (yoneda.map A.b) A.q (qm ≫ eP.hom) bY.hom :=
    hbYc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinr)
  have hback : i.hom ≫ aY.hom = fb.hom ≫ bY.hom := congrArg (fun φ => φ.hom) hE.w
  have hlift' : ∀ t : PullbackCone f₁ f₂, ∃ m : t.pt ⟶ ZF,
      (m ≫ a₁ = t.fst ∧ m ≫ a₂ = t.snd) ∧
        ∀ m' : t.pt ⟶ ZF, (m' ≫ a₁ = t.fst ∧ m' ≫ a₂ = t.snd) → m' = m := by
    intro t
    have hbase : t.fst.base ≫ f₁.base = t.snd.base ≫ f₂.base :=
      congrArg (fun g : t.pt ⟶ X => g.base) t.condition
    have hmaps : f₁.map ≫ t.fst.map = f₂.map ≫ t.snd.map :=
      congrArg (fun g : t.pt ⟶ X => g.map) t.condition
    let b : t.pt.base ⟶ P := hbp.lift t.fst.base t.snd.base hbase
    have hb₁ : b ≫ q₁ = t.fst.base := hbp.lift_fst _ _ _
    have hb₂ : b ≫ q₂ = t.snd.base := hbp.lift_snd _ _ _
    let tfst : sX X₁ ⟶ sX t.pt := ObjectProperty.homMk t.fst.map
    let tsnd : sX X₂ ⟶ sX t.pt := ObjectProperty.homMk t.snd.map
    have hjt : j₂ ≫ tsnd = j₁ ≫ tfst := ObjectProperty.hom_ext _ hmaps.symm
    let m : pushout j₂ j₁ ⟶ sX t.pt := hZpo.desc tsnd tfst hjt
    have hm₁ : c₁ ≫ m = tfst := hZpo.inr_desc _ _ _
    have hm₂ : c₂ ≫ m = tsnd := hZpo.inl_desc _ _ _
    -- the base change of `t.pt` to the spectrum of the fibre product
    let tb : sX t.pt ⟶ schemeSpace (spaceBaseOver B hΛ hSpec t.pt.base) :=
      ObjectProperty.homMk t.pt.toBase
    let sb := schemeSpaceMap (spaceBaseOverMap B hΛ hSpec b)
    have hWpb : IsPullback (pullback.fst tb sb) (pullback.snd tb sb) tb sb :=
      IsPullback.of_hasPullback _ _
    have hwflat : Space.IsFlat B (Spec (.of Λ)) hΛ (pullback.snd tb sb).hom := by
      let _ := Space.isFlat_isStableUnderBaseChange B (Spec (.of Λ)) hΛ
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃F G : AlgebraicSpaces B (Spec (.of Λ)) hΛ⦄ (g : F ⟶ G) =>
          Space.IsFlat B (Spec (.of Λ)) hΛ g.hom) hWpb
        (show Space.IsFlat B (Spec (.of Λ)) hΛ tb.hom from t.pt.flat)
    have hout₁ : IsPullback tfst v tb (bY ≫ sb) := by
      have h := t.fst.cartesian
      rw [← hb₁, spaceBaseOverMap_comp, Functor.map_comp] at h
      exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) h
    have hout₂ : IsPullback tsnd u' tb (aY ≫ sb) := by
      have h := t.snd.cartesian
      rw [← hb₂, spaceBaseOverMap_comp, Functor.map_comp] at h
      exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) h
    obtain ⟨e₁, hef₁, hes₁⟩ : ∃ e : sX X₁ ⟶ pullback tb sb,
        e ≫ pullback.fst tb sb = tfst ∧ e ≫ pullback.snd tb sb = v ≫ bY :=
      ⟨hWpb.lift tfst (v ≫ bY) (by rw [hout₁.w, Category.assoc]),
        hWpb.lift_fst _ _ _, hWpb.lift_snd _ _ _⟩
    obtain ⟨e₂, hef₂, hes₂⟩ : ∃ e : sX X₂ ⟶ pullback tb sb,
        e ≫ pullback.fst tb sb = tsnd ∧ e ≫ pullback.snd tb sb = u' ≫ aY :=
      ⟨hWpb.lift tsnd (u' ≫ aY) (by rw [hout₂.w, Category.assoc]),
        hWpb.lift_fst _ _ _, hWpb.lift_snd _ _ _⟩
    have he₁ : IsPullback e₁ v (pullback.snd tb sb) bY :=
      IsPullback.of_right (by rw [hef₁]; exact hout₁) hes₁ hWpb
    have he₂ : IsPullback e₂ u' (pullback.snd tb sb) aY :=
      IsPullback.of_right (by rw [hef₂]; exact hout₂) hes₂ hWpb
    have hcs : j₂ ≫ e₂ = j₁ ≫ e₁ := by
      refine hWpb.hom_ext ?_ ?_
      · simpa only [Category.assoc, hef₁, hef₂] using hjt
      · simpa only [Category.assoc, hes₁, hes₂] using hzw
    have hWpush : IsPushout j₂ j₁ e₂ e₁ :=
      isPushout_of_isFlat_of_thickeningAffineAtlas B (Spec (.of Λ)) hΛ A hqm'
        (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
        (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE) haX'' hbY'' hback hwflat
        (AlgebraicSpaces.isPullback_hom B (Spec (.of Λ)) hΛ he₂)
        (AlgebraicSpaces.isPullback_hom B (Spec (.of Λ)) hΛ he₁)
        (show IsPullback j₁.hom pX.hom v.hom fb.hom from f₁.cartesian)
        (show j₂.hom ≫ u'.hom = pX.hom ≫ i.hom from f₂.cartesian.w)
        (congrArg (fun φ => φ.hom) hcs).symm
    have hθ₁ : c₁ ≫ (hZpo.isoIsPushout _ _ hWpush).hom = e₁ :=
      hZpo.inr_isoIsPushout_hom _ _ hWpush
    have hθ₂ : c₂ ≫ (hZpo.isoIsPushout _ _ hWpush).hom = e₂ :=
      hZpo.inl_isoIsPushout_hom _ _ hWpush
    have hθfst : (hZpo.isoIsPushout _ _ hWpush).hom ≫ pullback.fst tb sb = m := by
      refine hZpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hθ₂, hef₂, hm₂]
      · rw [← Category.assoc, hθ₁, hef₁, hm₁]
    have hθsnd : (hZpo.isoIsPushout _ _ hWpush).hom ≫ pullback.snd tb sb = g := by
      refine hZpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hθ₂, hes₂, hgc₂]
      · rw [← Category.assoc, hθ₁, hes₁, hgc₁]
    have hcart : IsPullback m g tb sb := by
      refine hWpb.of_iso (hZpo.isoIsPushout _ _ hWpush).symm (Iso.refl _) (Iso.refl _)
        (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hθfst, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
      · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hθsnd, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
    have hcart' : IsPullback m.hom g.hom t.pt.toBase
        (yoneda.map (spaceBaseOverMap B hΛ hSpec b)) :=
      AlgebraicSpaces.isPullback_hom B (Spec (.of Λ)) hΛ hcart
    let mF : t.pt ⟶ ZF := { base := b, map := m.hom, cartesian := hcart' }
    refine ⟨mF, ⟨?_, ?_⟩, ?_⟩
    · exact FlatAlgebraicSpaceFamily.Hom.ext hb₁ (congrArg (fun φ => φ.hom) hm₁)
    · exact FlatAlgebraicSpaceFamily.Hom.ext hb₂ (congrArg (fun φ => φ.hom) hm₂)
    · intro m' hm'
      have hb' : m'.base = b := by
        refine hbp.hom_ext ?_ ?_
        · exact (congrArg (fun g : t.pt ⟶ X₁ => g.base) hm'.1).trans hb₁.symm
        · exact (congrArg (fun g : t.pt ⟶ X₂ => g.base) hm'.2).trans hb₂.symm
      let m'' : pushout j₂ j₁ ⟶ sX t.pt := ObjectProperty.homMk m'.map
      have hm'' : m'' = m := by
        refine hZpo.hom_ext ?_ ?_
        · exact ObjectProperty.hom_ext _
            ((congrArg (fun g : t.pt ⟶ X₂ => g.map) hm'.2).trans
              (congrArg (fun φ => φ.hom) hm₂).symm)
        · exact ObjectProperty.hom_ext _
            ((congrArg (fun g : t.pt ⟶ X₁ => g.map) hm'.1).trans
              (congrArg (fun φ => φ.hom) hm₁).symm)
      exact FlatAlgebraicSpaceFamily.Hom.ext hb' (congrArg (fun φ => φ.hom) hm'')
  refine ⟨PullbackCone.mk a₁ a₂ hw, ⟨?_⟩, ?_⟩
  · refine PullbackCone.IsLimit.mk hw (fun t => (hlift' t).choose) ?_ ?_ ?_
    · intro t; exact (hlift' t).choose_spec.1.1
    · intro t; exact (hlift' t).choose_spec.1.2
    · intro t m' h₁ h₂; exact (hlift' t).choose_spec.2 m' ⟨h₁, h₂⟩
  · refine ⟨IsLimit.ofIsoLimit hbp.isLimit (PullbackCone.ext (Iso.refl _) ?_ ?_)⟩
    · change q₁ = 𝟙 _ ≫ q₁
      simp
    · change q₂ = 𝟙 _ ≫ q₂
      simp

/-- **Stacks Project, Tag 0E40**, the in-particular clause. The deformation category of an
algebraic space `X` over the residue field `k` is a deformation category: a predeformation
category satisfying (RS).

It is the category of flat families lying over the family `(k, X)`, which lies over the residue
field, a terminal object of `𝒞_Λ`; condition (RS) for the category of all flat families is
`Deformation.Examples.satisfiesRS_flatAlgebraicSpaceFamilyFunctor`. -/
@[stacks 0E40 "the in-particular clause: the deformation category of an algebraic space over k \
is a deformation category"]
theorem isDeformationCategory_spaceDeformationProjection
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    IsDeformationCategory.{u, u, u} (spaceDeformationProjection B hΛ hSpec X hX toK) := by
  have hRS := satisfiesRS_flatAlgebraicSpaceFamilyFunctor B hΛ hSpec
  let p := flatAlgebraicSpaceFamilyFunctor B hΛ hSpec
  let x := spaceSpecialFiber B hΛ hSpec X hX toK
  have ht : IsTerminal (p.obj x) := isTerminal_residueFieldBase
  have hs : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k))
  refine ⟨⟨isCofiberedInGroupoids_overForget hRS.1 x ht, ?_⟩, ?_⟩
  · exact objectsOverFunctor_fiber_equiv_punit_of_isTerminal p hRS.1 x ht _ hs
  · exact satisfiesRS_objectsOverFunctor_of_isTerminal p hRS x ht

end Deformation.Examples

end
