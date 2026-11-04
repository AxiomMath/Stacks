module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityChartRigidity
public import StacksFrontier.AlgebraicGeometry.Descent.PulledBackDatumComposition

/-!
# Restricting a chart of a descent datum to a smaller open of the base

Let `𝒰 = {X i ⟶ S}` be a family of morphisms of schemes with fixed target, let `D` be a descent
datum relative to it, and let `V ≤ U` be opens of `S`. Restricting `𝒰` over `U` and then over
`V` is restricting it over `V`, so the datum restricted to `U` pulls back to the datum restricted
to `V`; consequently a chart of the datum restricted to `U` gives, by base change along the
inclusion of `V` into `U`, a chart of the datum restricted to `V`.

This file produces, out of a chart `C_U` of the datum restricted to `U` and a chart `C_V` of the
datum restricted to `V`, the comparison morphism between the two schemes over the base which
exhibits the one over `V` as the part of the one over `U` lying over `V`, and computes it on the
projections of the charts.

## Main definitions

* `AlgebraicGeometry.PreZeroHypercover.restrictBaseHomOver` and
  `AlgebraicGeometry.MorphismOfSchemeFamilies.ofRestrictBaseLE`: the restriction morphism of
  families attached to an inclusion `V ≤ U` of opens of the base.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.ofRestrictBaseAux`: the morphism of families
  restricting `𝒰` to an open of the base, with the comparison morphisms of the members supplied
  as a parameter rather than fixed to the inclusions of the preimages.
* `AlgebraicGeometry.DescentData.restrictBaseLEIso`: the identification of the datum restricted
  to `V` with the pullback along the restriction morphism of families of the datum restricted to
  `U`.

## Main results

* `AlgebraicGeometry.DescentData.Chart.exists_isPullback_comp`: if one chart of a datum relative
  to a covering family for the fpqc topology is a base change along a morphism out of the base,
  then so is every other chart, compatibly with the projections.
* `AlgebraicGeometry.DescentData.exists_isPullback_restrictBase`: the comparison morphism between
  the schemes charting a descent datum over two nested opens of the base. It exhibits the scheme
  over `V` as the part of the scheme over `U` lying over `V`, and on the projections of the charts
  it is the canonical map between the corresponding components of the two restricted data.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S : Scheme.{u}}

/-! ### The inverse of the collapse of an iterated fibre product -/

/-- The inverse of `pullbackCompObjIso W a g b hw`, followed by the projection of
`(W ×_S Y) ×_Y X` to `W`, is the first projection of `W ×_S X`. -/
@[reassoc]
lemma pullbackCompObjIso_inv_left_fst_fst (W : Over S) {X Y : Scheme.{u}}
    (a : X ⟶ Y) (g : Y ⟶ S) (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjIso W a g b hw).inv.left ≫
        pullback.fst (pullback.snd W.hom g) a ≫ pullback.fst W.hom g =
      pullback.fst W.hom b := by
  rw [← pullbackCompObjIso_hom_left_fst W a g b hw, ← Category.assoc, ← Over.comp_left,
    Iso.inv_hom_id, Over.id_left, Category.id_comp]

/-- The inverse of `pullbackCompObjIso W a g b hw`, followed by the projection of
`(W ×_S Y) ×_Y X` to `Y` through `W ×_S Y`, is the second projection of `W ×_S X` followed
by `a`. -/
@[reassoc]
lemma pullbackCompObjIso_inv_left_fst_snd (W : Over S) {X Y : Scheme.{u}}
    (a : X ⟶ Y) (g : Y ⟶ S) (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjIso W a g b hw).inv.left ≫
        pullback.fst (pullback.snd W.hom g) a ≫ pullback.snd W.hom g =
      pullback.snd W.hom b ≫ a := by
  rw [pullback.condition, ← Category.assoc]
  congr 1
  simpa only [Over.pullback_obj_hom] using Over.w (pullbackCompObjIso W a g b hw).inv

/-! ### The restriction morphism of families -/

/-- The restriction morphism of families attached to an inclusion `V ≤ U` of opens of the base:
its comparison morphism at `i` is the inclusion of `(f i)⁻¹(V)` into `(f i)⁻¹(U)`. -/
abbrev PreZeroHypercover.restrictBaseHomOver (𝒰 : PreZeroHypercover.{u} S) {V U : S.Opens}
    (h : V ≤ U) :
    (PreZeroHypercover.restrictBase 𝒰 V).HomOver (PreZeroHypercover.restrictBase 𝒰 U)
      (S.homOfLE h) where
  s₀ i := i
  h₀ i := (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)
  w₀ i := (morphismRestrict_homOfLE (𝒰.f i) V U h).symm

/-- Restricting a family to a smaller open of the base, as a morphism of families. -/
abbrev MorphismOfSchemeFamilies.ofRestrictBaseLE (𝒰 : PreZeroHypercover.{u} S) {V U : S.Opens}
    (h : V ≤ U) : MorphismOfSchemeFamilies.{u} :=
  MorphismOfSchemeFamilies.ofHomOver (PreZeroHypercover.restrictBase 𝒰 V)
    (PreZeroHypercover.restrictBase 𝒰 U) (S.homOfLE h)
    (PreZeroHypercover.restrictBaseHomOver 𝒰 h)

/-- The morphism of families restricting `𝒰` to an open `V` of the base, with the comparison
morphisms of the members supplied as a parameter.

Taking them to be the inclusions of the preimages gives
`AlgebraicGeometry.MorphismOfSchemeFamilies.ofRestrictBase`; taking them to be the inclusion of
`(f i)⁻¹(V)` into `(f i)⁻¹(U)` followed by the inclusion of `(f i)⁻¹(U)` gives the composite of
two restrictions. -/
abbrev MorphismOfSchemeFamilies.ofRestrictBaseAux (𝒰 : PreZeroHypercover.{u} S) (V : S.Opens)
    (a : ∀ i, ((𝒰.f i) ⁻¹ᵁ V).toScheme ⟶ 𝒰.X i)
    (wa : ∀ i, a i ≫ 𝒰.f i = ((𝒰.f i) ∣_ V) ≫ V.ι) : MorphismOfSchemeFamilies.{u} where
  sourceBase := V.toScheme
  targetBase := S
  sourceFamily := PreZeroHypercover.restrictBase 𝒰 V
  targetFamily := 𝒰
  baseHom := V.ι
  familyHom := { s₀ := fun i ↦ i, h₀ := a, w₀ := wa }

/-! ### Comparison of charts -/

/-- If one chart of a datum relative to a covering family for the fpqc topology is the base
change of a scheme along a morphism out of the base, then so is every other chart, compatibly with
the projections. -/
lemma DescentData.Chart.exists_isPullback_comp {B : Scheme.{u}} {𝒱 : PreZeroHypercover.{u} B}
    (h𝒱 : Presieve.ofArrows 𝒱.X 𝒱.f ∈ Scheme.fpqcPrecoverage B) {D' : DescentData 𝒱.f}
    (CV C' : D'.Chart) {Y W : Scheme.{u}} (p : C'.base.left ⟶ Y) (g : B ⟶ W) (q : Y ⟶ W)
    (hsq : IsPullback p C'.base.hom q g) :
    ∃ r : CV.base.left ⟶ Y, IsPullback r CV.base.hom q g ∧
      ∀ i, CV.proj i ≫ r = C'.proj i ≫ p := by
  have hw := Over.w (DescentData.Chart.isoOfCharts h𝒱 CV C').hom
  have hiso : IsIso (DescentData.Chart.isoOfCharts h𝒱 CV C').hom.left :=
    (Over.forget B).map_isIso (DescentData.Chart.isoOfCharts h𝒱 CV C').hom
  refine ⟨(DescentData.Chart.isoOfCharts h𝒱 CV C').hom.left ≫ p, ?_, fun i ↦ ?_⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩
      (asIso (DescentData.Chart.isoOfCharts h𝒱 CV C').hom.left ≪≫ hsq.isoPullback) ?_ ?_
    · rw [Category.assoc, hsq.w, ← Category.assoc, hw]
    · rw [Iso.trans_hom, Category.assoc, hsq.isoPullback_hom_fst, asIso_hom]
    · rw [Iso.trans_hom, Category.assoc, hsq.isoPullback_hom_snd, asIso_hom, hw]
  · rw [← Category.assoc, DescentData.Chart.proj_comp_isoOfCharts_hom]

section Restriction

open MorphismOfSchemeFamilies

attribute [local implicit_reducible] MorphismOfSchemeFamilies.pulledBackDatum
  MorphismOfSchemeFamilies.ofRestrictBase MorphismOfSchemeFamilies.pullbackFunctor
  CategoryTheory.PreZeroHypercover.HomOver.comp

/-- Pulling the restriction of a datum to `U` back along the restriction morphism of families
attached to `V ≤ U` is restricting the datum to `V`. -/
abbrev DescentData.restrictBaseLEIso (𝒰 : PreZeroHypercover.{u} S) (D : DescentData 𝒰.f)
    {V U : S.Opens} (h : V ≤ U) :=
  pulledBackDatumCompIso (PreZeroHypercover.restrictBaseHomOver 𝒰 h)
    (ofRestrictBase 𝒰 U).familyHom (S.homOfLE_ι h) D

/-- The comparison morphism between the schemes charting a descent datum over two nested opens
of the base, with the restriction morphism of families written as a composite. -/
lemma DescentData.exists_isPullback_restrictBase_comp (𝒰 : PreZeroHypercover.{u} S)
    (D : DescentData 𝒰.f) {V U : S.Opens} (h : V ≤ U)
    (CU : (pulledBackDatum (ofRestrictBase 𝒰 U) D).Chart)
    (hV : Presieve.ofArrows (PreZeroHypercover.restrictBase 𝒰 V).X
      (PreZeroHypercover.restrictBase 𝒰 V).f ∈ Scheme.fpqcPrecoverage V.toScheme)
    (CV : (pulledBackDatum (ofHomOver (PreZeroHypercover.restrictBase 𝒰 V) 𝒰 V.ι
      ((PreZeroHypercover.restrictBaseHomOver 𝒰 h).comp
        (ofRestrictBase 𝒰 U).familyHom (S.homOfLE_ι h))) D).Chart) :
    ∃ r : CV.base.left ⟶ CU.base.left,
      IsPullback r CV.base.hom CU.base.hom (S.homOfLE h) ∧
      ∀ (i : 𝒰.I₀) (k : pullback (D.obj i).hom
            ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι) ⟶
          pullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι)),
        k ≫ pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
          pullback.fst (D.obj i).hom
            ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι) →
        k ≫ pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
          pullback.snd (D.obj i).hom
              ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι) ≫
            (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) →
        CV.proj i ≫ r = k ≫ CU.proj i := by
  obtain ⟨r, hr, hrproj⟩ := DescentData.Chart.exists_isPullback_comp hV CV
    (DescentData.Chart.ofIso (DescentData.restrictBaseLEIso 𝒰 D h)
      (DescentData.Chart.pulledBack (ofRestrictBaseLE 𝒰 h) CU))
    (pullback.fst CU.base.hom (S.homOfLE h)) (S.homOfLE h) CU.base.hom
    (IsPullback.of_hasPullback CU.base.hom (S.homOfLE h))
  refine ⟨r, hr, fun i k hk₁ hk₂ ↦ ?_⟩
  have hid : ∀ {Z : Scheme.{u}}
      (p : ((pulledBackDatum (ofRestrictBaseLE 𝒰 h)
        (pulledBackDatum (ofRestrictBase 𝒰 U) D)).obj i).left ⟶ Z),
      (pulledBackDatumObjIso (ofRestrictBaseLE 𝒰 h)
        (pulledBackDatum (ofRestrictBase 𝒰 U) D) i).hom.left ≫ p = p :=
    fun p ↦ Category.id_comp p
  have hX : ((DescentData.restrictBaseLEIso 𝒰 D h).inv.hom i).left ≫
        pullback.fst ((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom
          ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) ≫
        pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      pullback.fst (D.obj i).hom
        ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι) :=
    pullbackCompObjIso_inv_left_fst_fst (D.obj i)
      ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) (((𝒰.f i) ⁻¹ᵁ U).ι) _ rfl
  have hY : ((DescentData.restrictBaseLEIso 𝒰 D h).inv.hom i).left ≫
        pullback.fst ((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom
          ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) ≫
        pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
      pullback.snd (D.obj i).hom
          ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι) ≫
        (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) :=
    pullbackCompObjIso_inv_left_fst_snd (D.obj i)
      ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) (((𝒰.f i) ⁻¹ᵁ U).ι) _ rfl
  have hkey : k = ((DescentData.restrictBaseLEIso 𝒰 D h).inv.hom i).left ≫
      pullback.fst ((pulledBackDatum (ofRestrictBase 𝒰 U) D).obj i).hom
        ((𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h)) :=
    pullback.hom_ext (hk₁.trans ((Category.assoc _ _ _).trans hX).symm)
      (hk₂.trans ((Category.assoc _ _ _).trans hY).symm)
  refine (hrproj i).trans <|
    (eq_whisker (DescentData.Chart.ofIso_proj (DescentData.restrictBaseLEIso 𝒰 D h)
      (DescentData.Chart.pulledBack (ofRestrictBaseLE 𝒰 h) CU) i) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (DescentData.Chart.pulledBack_proj (ofRestrictBaseLE 𝒰 h) CU i)).trans ?_
  rw [hid, hkey]
  exact (Category.assoc _ _ _).symm

/-- The comparison morphism between the schemes charting a descent datum over two nested opens
`V ≤ U` of the base. It exhibits the scheme over `V` as the part of the scheme over `U` lying over
`V`, and composing it with the projection of the chart over `V` is `k` followed by the projection
of the chart over `U`, for any map `k` between the corresponding components of the two restricted
data with the two prescribed projections out of the fibre product. -/
lemma DescentData.exists_isPullback_restrictBase (𝒰 : PreZeroHypercover.{u} S)
    (D : DescentData 𝒰.f) {V U : S.Opens} (h : V ≤ U)
    (CU : (pulledBackDatum (ofRestrictBase 𝒰 U) D).Chart)
    (a : ∀ i, ((𝒰.f i) ⁻¹ᵁ V).toScheme ⟶ 𝒰.X i)
    (wa : ∀ i, a i ≫ 𝒰.f i = ((𝒰.f i) ∣_ V) ≫ V.ι)
    (ha : a = fun i ↦ (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) ≫ ((𝒰.f i) ⁻¹ᵁ U).ι)
    (hV : Presieve.ofArrows (PreZeroHypercover.restrictBase 𝒰 V).X
      (PreZeroHypercover.restrictBase 𝒰 V).f ∈ Scheme.fpqcPrecoverage V.toScheme)
    (CV : (pulledBackDatum (ofRestrictBaseAux 𝒰 V a wa) D).Chart) :
    ∃ r : CV.base.left ⟶ CU.base.left,
      IsPullback r CV.base.hom CU.base.hom (S.homOfLE h) ∧
      ∀ (i : 𝒰.I₀)
        (k : pullback (D.obj i).hom (a i) ⟶ pullback (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι)),
        k ≫ pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
          pullback.fst (D.obj i).hom (a i) →
        k ≫ pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U).ι) =
          pullback.snd (D.obj i).hom (a i) ≫
            (𝒰.X i).homOfLE ((𝒰.f i).preimage_mono h) →
        CV.proj i ≫ r = k ≫ CU.proj i := by
  subst ha
  exact DescentData.exists_isPullback_restrictBase_comp 𝒰 D h CU hV CV

end Restriction

end AlgebraicGeometry

end

end
