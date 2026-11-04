module

public import StacksFrontier.AlgebraicGeometry.Quot.FibreRestrictionGluing
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnitFlatEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement

/-!
# Restriction for `Spaces'_{flat, lfp}` across an affine thickening pushout

Let
```
T  ⟶ T'
↓     ↓
S  ⟶ S'
```
be a pushout of schemes of the big fppf site in which `T ⟶ T'` is a thickening and `T ⟶ S` is
affine (Stacks 07RT). This file reads the gluing results of Stacks 07VY, 07W0 and 07W3 for
algebraic spaces as the statement `AlgebraicGeometry.Space.FlatLfpPushoutRS`: restriction from
the flat algebraic spaces locally of finite presentation over `S'` to compatible pairs over `S`
and `T'` is an equivalence of fibre categories. That statement is the input to which
`AlgebraicGeometry.Space.properPushoutRS_of_flatLfpPushoutRS` reduces Stacks 0D1J, and through
it `AlgebraicGeometry.curvePushoutEquivalence` reduces Stacks 0D56.

The two hypotheses of `AlgebraicGeometry.Space.fibreRestriction_isEquivalence_of_isPushout_of_glue`
are verified:

* every algebraic space `W` flat over `S'` is the pushout of its restrictions to `S`, `T` and
  `T'` — the counit assertion of Stacks 07W3, in the form
  `AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas`, transported from the
  pushout of the atlas to `S'` along Stacks 07SY;
* a compatible pair `(V, U', φ)` of flat algebraic spaces locally of finite presentation is glued
  by the pushout `V ⨿_{V ×_S T} U'`, which recovers `V` and `U'` by base change (Stacks 07W0,
  `AlgebraicGeometry.Space.ThickeningAffineGluingChart.isPullback_v` and `isPullback_u'`) and is
  flat and locally of finite presentation over `S'` (clause (3) of Stacks 07W3, in the form
  `ThickeningAffineGluingChart.isFlat_and_isLocallyOfFinitePresentation_iff`).

Both rest on the chart lift `AlgebraicGeometry.Space.HasEtaleChartLifts` — the chart form of the
essential surjectivity half of Stacks 05ZS — through which the gluing results are presently
available, and which is the only input of the main result.

## Main results

* `AlgebraicGeometry.Space.isPushoutOfRestrictions_flatLfp`: flat objects over `S'` are pushouts
  of their restrictions.
* `AlgebraicGeometry.Space.gluesCompatiblePairs_flatLfp`: compatible pairs glue.
* `AlgebraicGeometry.Space.flatLfpPushoutRS_of_hasEtaleChartLifts`: the statement
  `AlgebraicGeometry.Space.FlatLfpPushoutRS`, given that charts lift across thickenings.
* `AlgebraicGeometry.Space.properPushoutRS_of_hasEtaleChartLifts` and
  `AlgebraicGeometry.curvePushoutEquivalence_of_hasEtaleChartLifts`: the conclusions of
  Stacks 0D1J and Stacks 0D56, given that charts lift across thickenings.

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}
variable {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')

/-- A morphism of the site whose underlying morphism of schemes is affine gives an affine
morphism of algebraic spaces. -/
private theorem isAffineHom_schemeSpaceMap_hom
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f)) :
    IsAffineHom B S₀ hS₀ (schemeSpaceMap f).hom :=
  isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S₀ hS₀
    (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance f).mpr hf)

/-- Stacks 07SY for the square of algebraic spaces of a pushout square of schemes of the site. -/
private theorem isPushout_schemeSpaceMap
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map i))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f))
    (hsq : IsPushout ((BigFppfOver.toScheme B S₀ hS₀).map i)
      ((BigFppfOver.toScheme B S₀ hS₀).map f) ((BigFppfOver.toScheme B S₀ hS₀).map g)
      ((BigFppfOver.toScheme B S₀ hS₀).map h)) :
    IsPushout (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g) (schemeSpaceMap h) :=
  have := hf
  isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S₀ hS₀ i f g h hi hsq

variable (hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g)

/-- The square of base changes of an object `W` over `S'` to `T`, `T'` and `T'`: the map
`W_T ⟶ W_{T'}` lies over the thickening `T ⟶ T'`. -/
private theorem overlapToT'_snd (W : Over (schemeSpace S')) :
    overlapToT' i f g h hc W ≫ pullback.snd W.hom (schemeSpaceMap g) =
      pullback.snd (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
        schemeSpaceMap i := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ schemeSpaceMap i)
    (sliceOverlapIso_hom_left_comp_snd _ _ _ _ hc W)

/-- Postcomposing a cospan of a pullback square with an isomorphism on the common target. -/
private theorem isPullback_comp_hom_of_iso {C : Type*} [Category C] {P X Y Z Z' : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} {g' : Y ⟶ Z'}
    (h : IsPullback fst snd f g) (e : Z ≅ Z') (hg : g ≫ e.hom = g') :
    IsPullback fst snd (f ≫ e.hom) g' := by
  subst hg
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp) (by simp)

/-- **Flat objects over the pushout are pushouts of their restrictions.** For an affine
thickening pushout, every algebraic space flat and locally of finite presentation over `S'` is
the pushout of its restrictions to `S`, `T` and `T'`. This is the counit assertion of
Stacks 07W3. -/
theorem isPushoutOfRestrictions_flatLfp (hatlas : HasThickeningAffineAtlases B S₀ hS₀)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map i))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f))
    (hsq : IsPushout ((BigFppfOver.toScheme B S₀ hS₀).map i)
      ((BigFppfOver.toScheme B S₀ hS₀).map f) ((BigFppfOver.toScheme B S₀ hS₀).map g)
      ((BigFppfOver.toScheme B S₀ hS₀).map h)) :
    IsPushoutOfRestrictions (flatLfpProperty B S₀ hS₀) i f g h hc := by
  intro W
  have hi' := isThickeningHom_schemeSpaceMap i hi
  have hf' := isAffineHom_schemeSpaceMap_hom f hf
  have hE := isPushout_schemeSpaceMap i f g h hi hf hsq
  obtain ⟨A⟩ := hatlas _ _ hi' hf'
  obtain ⟨Epo, aY, bY, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S₀ hS₀ A hi'
  let eP : Epo.1 ≅ (schemeSpace S').1 :=
    { hom := (hpush.isoIsPushout _ _ hE).hom.hom
      inv := (hpush.isoIsPushout _ _ hE).inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) (hpush.isoIsPushout _ _ hE).hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) (hpush.isoIsPushout _ _ hE).inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = (schemeSpaceMap g).hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have hinr : bY.hom ≫ eP.hom = (schemeSpaceMap h).hom :=
    congrArg (fun φ => φ.hom) (hpush.inr_isoIsPushout_hom _ _ hE)
  have hqm' := isPullback_comp_hom_of_iso hqm eP rfl
  have haX'' := isPullback_comp_hom_of_iso haX' eP hinl
  have hbY'' := isPullback_comp_hom_of_iso hbYc eP hinr
  have hback : (schemeSpaceMap i).hom ≫ (schemeSpaceMap g).hom =
      (schemeSpaceMap f).hom ≫ (schemeSpaceMap h).hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun φ => φ.hom) hc.symm
  have hjX'w := congrArg (fun φ => φ.hom) (overlapToT'_snd i f g h hc W.obj)
  have hsides := congrArg (fun φ => φ.hom) (overlapToT'_fst i f g h hc W.obj).symm
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hjX'w hsides
  exact isPushout_of_isFlat_of_thickeningAffineAtlas B S₀ hS₀ A hqm'
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE) haX'' hbY'' hback W.property.1
    (AlgebraicSpaces.isPullback_hom B S₀ hS₀ (IsPullback.of_hasPullback _ _))
    (AlgebraicSpaces.isPullback_hom B S₀ hS₀ (IsPullback.of_hasPullback _ _))
    (AlgebraicSpaces.isPullback_hom B S₀ hS₀ (IsPullback.of_hasPullback _ _)) hjX'w hsides

/-- **Compatible pairs glue.** For an affine thickening pushout, every compatible pair
`(V, U', φ)` of algebraic spaces flat and locally of finite presentation over `S` and `T'` is
glued by the pushout `W = V ⨿_{V ×_S T} U'`: the two pieces are recovered from `W` by base
change (Stacks 07W0) and `W` is flat and locally of finite presentation over `S'` (clause (3) of
Stacks 07W3). -/
theorem gluesCompatiblePairs_flatLfp (hlift : HasEtaleChartLifts B S₀ hS₀)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map i))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f))
    (hsq : IsPushout ((BigFppfOver.toScheme B S₀ hS₀).map i)
      ((BigFppfOver.toScheme B S₀ hS₀).map f) ((BigFppfOver.toScheme B S₀ hS₀).map g)
      ((BigFppfOver.toScheme B S₀ hS₀).map h)) :
    GluesCompatiblePairs (flatLfpProperty B S₀ hS₀) (flatLfpProperty_fibreStable B S₀ hS₀)
      i f g h := by
  intro P
  have hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g := by
    have hsite : f ≫ h = i ≫ g :=
      (BigFppfOver.toScheme B S₀ hS₀).map_injective
        (by simpa only [Functor.map_comp] using hsq.w.symm)
    calc schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap (f ≫ h) := by ext; rfl
      _ = schemeSpaceMap (i ≫ g) := by rw [hsite]
      _ = _ := by ext; rfl
  have hi' := isThickeningHom_schemeSpaceMap i hi
  have hf' := isAffineHom_schemeSpaceMap_hom f hf
  have hE := isPushout_schemeSpaceMap i f g h hi hf hsq
  let V : Over (schemeSpace S) := P.fst.obj
  let U' : Over (schemeSpace T') := P.snd.obj
  let φ : (Over.pullback (schemeSpaceMap f)).obj V ≅ (Over.pullback (schemeSpaceMap i)).obj U' :=
    (flatLfpProperty B S₀ hS₀ T).ι.mapIso P.iso
  have hφT : φ.hom.left ≫ pullback.snd U'.hom (schemeSpaceMap i) =
      pullback.snd V.hom (schemeSpaceMap f) := Over.w φ.hom
  let eφ := (Over.forget _).mapIso φ
  have hU' : IsPullback (φ.hom.left ≫ pullback.fst U'.hom (schemeSpaceMap i))
      (pullback.snd V.hom (schemeSpaceMap f)) U'.hom (schemeSpaceMap i) :=
    (IsPullback.of_hasPullback U'.hom (schemeSpaceMap i)).of_iso eφ.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (by simp [eφ]) (by simp [eφ, ← hφT]) (by simp) (by simp)
  have hV : IsPullback (pullback.fst V.hom (schemeSpaceMap f))
      (pullback.snd V.hom (schemeSpaceMap f)) V.hom (schemeSpaceMap f) :=
    IsPullback.of_hasPullback _ _
  have hthick : IsThickeningHom B S₀ hS₀ (φ.hom.left ≫ pullback.fst U'.hom (schemeSpaceMap i)) :=
    isThickeningHom_of_isPullback B S₀ hS₀ hU'.flip hi'
  have haff : IsAffineHom B S₀ hS₀ (pullback.fst V.hom (schemeSpaceMap f)).hom :=
    isAffineHom_hom_of_isPullback hV.flip hf'
  have := hasPushout_of_isThickening_of_isAffineHom B S₀ hS₀
    (hasThickeningAffineAtlases_of_chartLift B S₀ hS₀ hlift) _ _ hthick haff
  have hG := IsPushout.of_hasPushout (φ.hom.left ≫ pullback.fst U'.hom (schemeSpaceMap i))
    (pullback.fst V.hom (schemeSpaceMap f))
  have hcond : (φ.hom.left ≫ pullback.fst U'.hom (schemeSpaceMap i)) ≫ U'.hom ≫
      schemeSpaceMap g = pullback.fst V.hom (schemeSpaceMap f) ≫ V.hom ≫ schemeSpaceMap h := by
    rw [hU'.w_assoc, hV.w_assoc, hc]
  let gm := pushout.desc (U'.hom ≫ schemeSpaceMap g) (V.hom ≫ schemeSpaceMap h) hcond
  have haG : pushout.inl _ _ ≫ gm = U'.hom ≫ schemeSpaceMap g := pushout.inl_desc _ _ _
  have hbG : pushout.inr _ _ ≫ gm = V.hom ≫ schemeSpaceMap h := pushout.inr_desc _ _ _
  obtain ⟨D, hV₁, hU₁, hY₁, hX₁⟩ := exists_thickeningAffineGluingChart_of_chartLift B S₀ hS₀
    hlift hi' hf' hE hU' hV hG haG hbG
  refine ⟨⟨Over.mk gm, (D.isFlat_and_isLocallyOfFinitePresentation_iff).2
    ⟨P.fst.property, P.snd.property⟩⟩, pushout.inr _ _, pushout.inl _ _, ?_, ?_, ?_⟩
  · exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_v hbG hV₁ hY₁).flip
  · exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_u' haG hU₁ hX₁).flip
  · exact (Category.assoc _ _ _).symm.trans hG.w

/-- **The statement `AlgebraicGeometry.Space.FlatLfpPushoutRS`, given that charts lift across
thickenings.** For every affine thickening pushout of schemes of the site, restriction from the
algebraic spaces flat and locally of finite presentation over the pushout to the compatible
pairs over the two pieces is an equivalence. -/
theorem flatLfpPushoutRS_of_hasEtaleChartLifts (hlift : HasEtaleChartLifts B S₀ hS₀) :
    FlatLfpPushoutRS B S₀ hS₀ := by
  intro T T' S S' i f g h hi hf hsq hc
  exact fibreRestriction_isEquivalence_of_isPushout_of_glue _ _ i f g h hc
    (isPushoutOfRestrictions_flatLfp i f g h hc
      (hasThickeningAffineAtlases_of_chartLift B S₀ hS₀ hlift :
        HasThickeningAffineAtlases B S₀ hS₀) hi hf hsq)
    (gluesCompatiblePairs_flatLfp i f g h hlift hi hf hsq)

/-- Stacks 0D1J's statement `AlgebraicGeometry.Space.ProperPushoutRS`, given that charts lift
across thickenings: `AlgebraicGeometry.Space.properPushoutRS_of_flatLfpPushoutRS` applied to
`AlgebraicGeometry.Space.flatLfpPushoutRS_of_hasEtaleChartLifts`. -/
noncomputable def properPushoutRS_of_hasEtaleChartLifts (hlift : HasEtaleChartLifts B S₀ hS₀) :
    ProperPushoutRS B S₀ hS₀ :=
  properPushoutRS_of_flatLfpPushoutRS (flatLfpPushoutRS_of_hasEtaleChartLifts hlift)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Stacks 0D56's conclusion `AlgebraicGeometry.CurvePushoutEquivalenceData`, given that charts
lift across thickenings: `AlgebraicGeometry.curvePushoutEquivalence` applied to
`AlgebraicGeometry.Space.properPushoutRS_of_hasEtaleChartLifts`. Once the chart lift is proved,
this is the whole of Stacks 0D56. -/
noncomputable def curvePushoutEquivalence_of_hasEtaleChartLifts
    (hlift : Space.HasEtaleChartLifts B integerBase hZ)
    {T T' S S' : B.Schemes}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (hi : Stacks.Thickenings.IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)]
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    CurvePushoutEquivalenceData B hZ i f g h :=
  curvePushoutEquivalence B hZ (Space.properPushoutRS_of_hasEtaleChartLifts hlift) i f g h hi hsq

end AlgebraicGeometry
