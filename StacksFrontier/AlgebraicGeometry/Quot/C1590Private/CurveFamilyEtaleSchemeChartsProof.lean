module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorLiftLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorLiftReduction
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorSheafFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyGoodDivisors
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilySchemeNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus

/-!
# Families of curves are étale locally schemes (the assembly of Stacks 0E6F)

This file assembles the proof that a family of curves `X ⟶ S` is a scheme étale locally on `S`,
the proposition `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`, from the steps of the
following route:

* P1, `AlgebraicGeometry.C1590Private.fibreGoodDivisorPair`: the fibre at a closed point carries
  two good effective Cartier divisors with finite disjoint supports;
* P2, `AlgebraicGeometry.C1590Private.divisorLiftReduction` applied to
  `AlgebraicGeometry.C1590Private.divisorLiftAtClosedFibreLocal`: such a divisor lifts, after an
  elementary étale base change, to a relative effective Cartier divisor of the family;
* P3, `AlgebraicGeometry.C1590Private.schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison`:
  two such lifts make the family a scheme over an open neighbourhood of the point;
* Stacks 0D55, `AlgebraicGeometry.C1590Private.descentObj_curvesProjectionOver`: a family over an
  affine base descends to a stage of its Noetherian approximation.

## The argument

Let `HasSchemeChartAt X s` say that `s` is in the image of an étale `U ⟶ S` over which `X` is a
scheme. Its locus is open (étale morphisms are open) and is preserved along étale morphisms of
families (`HasSchemeChartAt.of_hom`) and pulled back along arbitrary morphisms of families
(`HasSchemeChartAt.of_hom_target`).

1. A family with representable total space has a chart at every point.
2. At a closed point `s` of an affine Noetherian base: the residue point `Spec κ(s) ⟶ S` is a
   closed immersion and the fibre is a scheme `V`; P1 gives `E₁, E₂`; P2 applied twice gives
   étale `Y₂ ⟶ Y₁ ⟶ X` carrying lifts `D₁, D₂` (the first pulled back to `Y₂`); `Y₂` has an affine
   base, locally Noetherian being étale over `S`; P3 makes `Y₂` a scheme over an open `U' ∋ s`.
3. On an affine Noetherian base every point specializes to a closed point (the base is
   quasi-compact), so every point has a chart.
4. On an affine base the family descends to a Noetherian affine stage (0D55), whose charts pull
   back.
5. In general, restrict to an affine open neighbourhood.

## Main definitions

* `AlgebraicGeometry.C1590Private.HasSchemeChartAt`: a scheme chart of a family at a point.

## Main results

* `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`: families of curves are étale locally
  schemes, `HasEtaleLocalSchemeCharts B hZ`.
* `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts_of`: the same from
  `FibreDivisorSheafComparison`, which is `fibreDivisorSheafComparison`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A scheme chart of a family of curves at a point `s` of its base: an étale morphism
`φ : U ⟶ S` of the site with `s` in its image, over which the family is represented by a scheme
`Z` of the site over `U`. `HasEtaleLocalSchemeCharts` asks for one at every point. -/
def HasSchemeChartAt (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : Prop :=
  ∃ (U Z : BigFppfOver B integerBase hZ) (φ : U ⟶ X.base) (q : Z ⟶ U)
    (p : schemeSpace Z ⟶ X.total),
    Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)

/-- **The chart locus is closed under generization**: the image of an étale morphism is open. -/
theorem HasSchemeChartAt.of_specializes {X : CurveFamily B hZ}
    {s s₀ : (BigFppfOver.toScheme B integerBase hZ).obj X.base} (h : HasSchemeChartAt X s₀)
    (hs : s ⤳ s₀) : HasSchemeChartAt X s := by
  obtain ⟨U, Z, φ, q, p, het, hs₀, hpb⟩ := h
  exact ⟨U, Z, φ, q, p, het,
    hs.mem_open ((BigFppfOver.toScheme B integerBase hZ).map φ).isOpenMap.isOpen_range hs₀, hpb⟩

/-- **Charts push forward along étale morphisms of families**: a chart of `Y` composed with an
étale morphism of families `Y ⟶ X` is a chart of `X`. -/
theorem HasSchemeChartAt.of_hom {X Y : CurveFamily B hZ} (g : Y ⟶ X)
    (hg : Etale ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap))
    {y : (BigFppfOver.toScheme B integerBase hZ).obj Y.base} (h : HasSchemeChartAt Y y) :
    HasSchemeChartAt X ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap y) := by
  obtain ⟨U, Z, φ, q, p, het, ⟨u, rfl⟩, hpb⟩ := h
  refine ⟨U, Z, φ ≫ g.baseMap, q, p ≫ g.totalMap, ?_, ⟨u, ?_⟩, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply]
  · rw [schemeSpaceMap_comp]
    exact hpb.paste_horiz g.cartesian

/-- **Charts pull back along morphisms of families**: if `g : X ⟶ X'` is a morphism of families
and `X'` has a chart at the image of `s`, then its base change is a chart of `X` at `s`. -/
theorem HasSchemeChartAt.of_hom_target {X X' : CurveFamily B hZ} (g : X ⟶ X')
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base}
    (h : HasSchemeChartAt X' ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap s)) :
    HasSchemeChartAt X s := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨U', Z', φ', q', p', het, ⟨u, hu⟩, hpb⟩ := h
  obtain ⟨w, hw⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq g.baseMap φ'
    (y := s) (z := u) hu.symm
  have hpbU := IsPullback.of_hasPullback g.baseMap φ'
  have hpbZ := IsPullback.of_hasPullback q' (pullback.snd g.baseMap φ')
  have hbot : schemeSpaceMap (pullback.snd g.baseMap φ') ≫ schemeSpaceMap φ' =
      schemeSpaceMap (pullback.fst g.baseMap φ') ≫ schemeSpaceMap g.baseMap := by
    rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, pullback.condition]
  have houter := (isPullback_schemeSpaceMap hpbZ).paste_horiz hpb
  let p : schemeSpace (pullback q' (pullback.snd g.baseMap φ')) ⟶ X.total :=
    g.cartesian.lift (schemeSpaceMap (pullback.fst q' (pullback.snd g.baseMap φ')) ≫ p')
      (schemeSpaceMap (pullback.snd q' (pullback.snd g.baseMap φ')) ≫
        schemeSpaceMap (pullback.fst g.baseMap φ'))
      (by rw [houter.w, hbot, Category.assoc])
  refine ⟨pullback g.baseMap φ', pullback q' (pullback.snd g.baseMap φ'),
    pullback.fst g.baseMap φ', pullback.snd q' (pullback.snd g.baseMap φ'), p, ?_, ⟨w, hw⟩, ?_⟩
  · exact MorphismProperty.of_isPullback (hpbU.map T).flip het
  · refine IsPullback.of_right ?_ (g.cartesian.lift_snd _ _ _) g.cartesian
    rw [g.cartesian.lift_fst, ← hbot]
    exact houter

/-- **A family with representable total space has a chart at every point**: the identity of the
base, with the scheme representing the total space. -/
theorem hasSchemeChartAt_of_isRepresentable (X : CurveFamily B hZ)
    (hX : X.total.obj.IsRepresentable) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    HasSchemeChartAt X s := by
  let e : schemeSpace (CurveFamily.totalSite hX) ≅ X.total :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (CurveFamily.totalSiteIso hX)
  have hid : schemeSpaceMap (𝟙 X.base) = 𝟙 (schemeSpace X.base) :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  refine ⟨X.base, CurveFamily.totalSite hX, 𝟙 _, CurveFamily.totalSiteToBase hX, e.hom, ?_,
    ⟨s, rfl⟩, ?_⟩
  · rw [CategoryTheory.Functor.map_id]
    infer_instance
  · have : IsIso (schemeSpaceMap (𝟙 X.base)) := by rw [hid]; infer_instance
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    apply ObjectProperty.hom_ext
    rw [hid, Category.comp_id]
    exact (CurveFamily.yoneda_map_totalSiteToBase hX).symm

/-- **Reduction to an affine base.** If every family over an affine base has charts at all
points, so does every family: restrict to an affine open neighbourhood of the point, an open
immersion being étale. -/
theorem hasSchemeChartAt_of_isAffine
    (h : ∀ X : CurveFamily B hZ, IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
      ∀ s, HasSchemeChartAt X s)
    (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    HasSchemeChartAt X s := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, -⟩ :=
    ((BigFppfOver.toScheme B integerBase hZ).obj X.base).isBasis_affineOpens
      |>.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let Wo : BigFppfOver B integerBase hZ :=
    Over.mk (⟨Scheme.Opens.ι W ≫ X.base.hom.hom⟩ :
      B.obj (Scheme.size_lt_of_isOpenImmersion (Scheme.Opens.ι W) X.base.left.property) ⟶ B.obj hZ)
  let j : Wo ⟶ X.base := Over.homMk ⟨Scheme.Opens.ι W⟩ rfl
  have hsq := IsPullback.of_hasPullback X.toBase (schemeSpaceMap j)
  exact (h (curveFamilyOfIsPullback X j _ _ hsq) hW ⟨s, hsW⟩).of_hom
    (curveFamilyOfIsPullbackHom X j _ _ hsq) (inferInstanceAs (Etale (Scheme.Opens.ι W)))

/-- **Reduction to a Noetherian affine base** (Stacks 0D55). A family of curves over an affine
base is the base change of a family over a stage of the Noetherian approximation of the base,
whose charts pull back. -/
theorem hasSchemeChartAt_of_isNoetherian
    (h : ∀ X : CurveFamily B hZ,
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base) → ∀ s,
      HasSchemeChartAt X s)
    (X : CurveFamily B hZ) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : HasSchemeChartAt X s := by
  obtain ⟨i, ⟨Y, hY⟩, δ, -⟩ := descentObj_curvesProjectionOver
    (affineSiteStageDiagram B hZ X.base) (isLimit_affineSiteStageCone B hZ X.base)
    (Functor.Fiber.mk (p := curvesProjectionOver B hZ) (a := X) rfl)
  change Y.base = ((affineSiteStageDiagram B hZ X.base).obj i).1 at hY
  exact (h Y (hY ▸ ((affineSiteStageDiagram B hZ X.base).obj i).2)
    (hY ▸ isNoetherian_affineSiteStageDiagram_obj B hZ X.base i) _).of_hom_target δ

/-- **Reduction to closed points.** On a quasi-compact base, a point specializes to a closed point,
and the chart locus is closed under generization. -/
theorem hasSchemeChartAt_of_isClosed_singleton (X : CurveFamily B hZ)
    [CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    (h : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base, IsClosed {s} →
      HasSchemeChartAt X s)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : HasSchemeChartAt X s := by
  obtain ⟨s₀, hs₀, hcl⟩ := (isClosed_closure (s := {s})).exists_closed_singleton
    ⟨s, subset_closure rfl⟩
  exact (h s₀ hcl).of_specializes (specializes_iff_mem_closure.2 hs₀)

variable (B hZ) in
/-- **A family of curves over an affine Noetherian base has a scheme chart at a closed point.**
The fibre `V` at the residue point carries two good divisors `E₁, E₂` (P1); lift `E₁` over an
étale `Y₁ ⟶ X` and `E₂` over an étale `Y₂ ⟶ Y₁` (P2); pull the first lift back to `Y₂`; then the
family `Y₂`, over an affine base which is locally Noetherian being étale over `S`, is a scheme over
an open neighbourhood `U'` of the point (P3). -/
theorem hasSchemeChartAt_of_isClosed (hP2 : DivisorLiftAtClosedFibre B hZ)
    (hP3 : SchemeNearFibreOfGoodDivisors B hZ (IsGoodFibreDivisor B hZ))
    (X : CurveFamily B hZ) (hX : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (hXn : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (hs : IsClosed {s}) :
    HasSchemeChartAt X s := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let P := X.residueFieldPoint s
  have hPci : IsClosedImmersion (T.map P.value) :=
    isClosed_singleton_iff_isClosedImmersion.1 hs
  obtain ⟨V, v, q, hq⟩ := exists_presentation_of_fieldValuedPoint X P
  obtain ⟨E₁, E₂, hE₁, hE₂, hf₁, hf₂, hdisj, hg₁, hg₂⟩ :=
    fibreGoodDivisorPair B hZ X P hPci V v q hq
  -- lift `E₁`
  obtain ⟨Y₁, φ₁, t₁, q₁, D₁, het₁, ht₁, hci₁, hpb₁, hq₁, haff₁, hrel₁, hpre₁⟩ :=
    hP2 X hX P hPci V v q hq E₁ hE₁ hf₁
  let P₁ : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y₁.base).obj :=
    { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t₁ }
  -- lift `E₂` over `Y₁`
  obtain ⟨Y₂, φ₂, t₂, q₂, D₂, het₂, ht₂, hci₂, hpb₂, hq₂, haff₂, hrel₂, hpre₂⟩ :=
    hP2 Y₁ haff₁ P₁ hci₁ V v q₁ hpb₁ E₂ hE₂ hf₂
  let P₂ : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y₂.base).obj :=
    { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t₂ }
  -- the first lift, pulled back to `Y₂`
  let D₁' : Space.ClosedSubspaces B integerBase hZ Y₂.total.obj :=
    ⟨D₁.1.preimage φ₂.totalMap.hom, Space.isClosedSubspace_preimage B integerBase hZ
      φ₂.totalMap.hom D₁.1 Y₁.total.2 Y₂.total.2 D₁.2⟩
  have hrel₁' : Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y₂.toBase D₁' :=
    isRelativeEffectiveCartierDivisor_preimage_totalMap φ₂ het₂ D₁ hrel₁
  have hpre₁' : D₁'.1.preimage q₂ = (Space.closedSubspaceOfIdeal V E₁).1 := by
    show (D₁.1.preimage φ₂.totalMap.hom).preimage q₂ = _
    rw [← Subfunctor.preimage_comp, hq₂, hpre₁]
  -- the base of `Y₂` is locally Noetherian
  have hn₂ : IsLocallyNoetherian (T.obj Y₂.base) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map φ₂.baseMap ≫ T.map φ₁.baseMap)
  obtain ⟨U', j, hj, ⟨t, ht⟩, hrep⟩ := hP3 Y₂ haff₂ hn₂ P₂ hci₂ V v q₂ hpb₂ D₁' D₂ E₁ E₂
    hrel₁' hrel₂ hpre₁' hpre₂ hdisj hg₁ hg₂
  have htj : t ≫ j = t₂ := by
    apply yoneda.map_injective
    rw [ht, yonedaEquiv_symm_value]
  -- the base change of `Y₂` to `U'` is a scheme
  have hsq := IsPullback.of_hasPullback Y₂.toBase (schemeSpaceMap j)
  have h₃ := hrep (curveFamilyOfIsPullback Y₂ j _ _ hsq) (curveFamilyOfIsPullbackHom Y₂ j _ _ hsq)
    (𝟙 _) (Category.id_comp _)
  let x : T.obj P.siteObject := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum P.carrier)
  have hc := (((hasSchemeChartAt_of_isRepresentable _ h₃ (T.map t x)).of_hom
    (curveFamilyOfIsPullbackHom Y₂ j _ _ hsq) (inferInstanceAs (Etale (T.map j)))).of_hom φ₂
    het₂).of_hom φ₁ het₁
  have hx : T.map (((t ≫ j) ≫ φ₂.baseMap) ≫ φ₁.baseMap) x = s := by
    have ht₂' : t₂ ≫ φ₂.baseMap = t₁ := ht₂
    rw [htj, ht₂', ht₁]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [← hx]
  simp only [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hc

variable (B hZ) in
/-- **Families of curves are étale locally schemes** (the assembly of Stacks 0E6F), from the
comparison `FibreDivisorSheafComparison` of the last open piece of P3. The divisor lift P2 is
`divisorLiftReduction` applied to `divisorLiftAtClosedFibreLocal`, and P3 is
`schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison`. -/
theorem hasEtaleLocalSchemeCharts_of (hc : FibreDivisorSheafComparison B hZ) :
    HasEtaleLocalSchemeCharts B hZ := by
  have hP3 : SchemeNearFibreOfGoodDivisors B hZ (IsGoodFibreDivisor B hZ) :=
    schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison B hZ hc
  have hP2 : DivisorLiftAtClosedFibre B hZ :=
    divisorLiftReduction divisorLiftAtClosedFibreLocal
  intro X s
  refine hasSchemeChartAt_of_isAffine (fun X hX s => ?_) X s
  refine hasSchemeChartAt_of_isNoetherian (fun Y hYa hYn s => ?_) X s
  exact hasSchemeChartAt_of_isClosed_singleton Y
    (fun s hs => hasSchemeChartAt_of_isClosed B hZ hP2 hP3 Y hYa inferInstance s hs) s

variable (B hZ) in
/-- **Families of curves are étale locally schemes** (Stacks 0E6F, unregistered here): every family
of curves `X ⟶ S` is a scheme étale locally on `S`. Every point of `S` is in the image of an étale
morphism `U ⟶ S` of the site over which the base change of `X` is represented by a scheme. -/
theorem hasEtaleLocalSchemeCharts : HasEtaleLocalSchemeCharts B hZ :=
  hasEtaleLocalSchemeCharts_of B hZ (fibreDivisorSheafComparison B hZ)

end AlgebraicGeometry.C1590Private

end
