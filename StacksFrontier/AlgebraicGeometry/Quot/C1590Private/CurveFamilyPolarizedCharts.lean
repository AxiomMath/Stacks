module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RelativelyAmpleDivisorNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Families of curves are smooth locally polarized

Every family of curves `X ⟶ S` is *smooth locally polarized*
(`AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized`): through every point of `S` there is
an étale, hence smooth, morphism `U ⟶ S` of the site over which `X` is a scheme `Z` carrying an
invertible module ample relative to `Z ⟶ U`. With
`exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized` (in the namespace
`AlgebraicGeometry.CurveFamily`) this makes finitely many families over one base H-projective
schemes over a common étale neighbourhood of any point (Stacks 0E6F,
with the polarizations of Stacks 0DQ0).

This is step C of the route to the representability of the diagonal of
`Curves` (Stacks 0D53).

## Main definitions

* `AlgebraicGeometry.C1590Private.HasPolarizedChartAt`: a polarized étale scheme chart of a family
  at a point of its base.
* `AlgebraicGeometry.C1590Private.CurvesSmoothLocallyPolarized`: every family of curves is smooth
  locally polarized.

## Main results

* `AlgebraicGeometry.C1590Private.hasPolarizedChartAt_of_isRelativeEffectiveCartierDivisor`: a
  family with representable total space carrying a relative effective Cartier divisor whose fibre
  at a closed point is an ample effective Cartier divisor has a polarized chart there.
* `AlgebraicGeometry.C1590Private.hasPolarizedChartAt`: every family of curves has a polarized
  chart at every point.
* `AlgebraicGeometry.C1590Private.curvesSmoothLocallyPolarized`: the statement
  `CurvesSmoothLocallyPolarized`.

## The argument

The assembly of `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts` (Stacks 0E6F), redone
carrying the first lifted divisor. At a closed point `s` of an affine Noetherian base the fibre
`V` carries two good divisors `E₁, E₂` with `𝒪_V(E₁)` ample (P1 with ampleness,
`AlgebraicGeometry.C1590Private.fibreGoodDivisorPair_isAmple`); P2 lifts them to relative
effective Cartier divisors `D₁, D₂` after étale base changes, and P3 makes the family a scheme `Z`
over an open neighbourhood of `s`. On `Z` the divisor `D₁` is a closed subscheme flat over the
base with fibre `E₁` (`AlgebraicGeometry.Space.schemeSpaceIdeal`), and
`AlgebraicGeometry.C1590Private.exists_isRelativelyAmple_near_closedPoint` (Stacks 062Y, 0C4U and
0D2S) makes `𝒪_Z(D₁)` relatively ample over a smaller open neighbourhood. Polarized charts are
open in the base, push forward along étale morphisms of families and pull back along arbitrary
ones (Stacks 0893), so the reductions to closed points, to a Noetherian base (Stacks 0D55) and to
an affine base go through as for scheme charts.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A polarized scheme chart of a family of curves at a point `s` of its base: an étale morphism
`π : T' ⟶ S` of the site with `s` in its image, over which the family is represented by a scheme
`Z` carrying an invertible module ample relative to `Z ⟶ T'`. -/
def HasPolarizedChartAt (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : Prop :=
  ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
    Etale ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
    s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
    ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ T'),
      IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap π) ∧
      ∃ (L : ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules)
        (_ : IsInvertibleModule _ L),
        Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B integerBase hZ).map q) L

/-! ### The polarized chart locus -/

/-- **The polarized chart locus is closed under generization**: the image of an étale morphism
is open. -/
theorem HasPolarizedChartAt.of_specializes {X : CurveFamily B hZ}
    {s s₀ : (BigFppfOver.toScheme B integerBase hZ).obj X.base} (h : HasPolarizedChartAt X s₀)
    (hs : s ⤳ s₀) : HasPolarizedChartAt X s := by
  obtain ⟨T', π, het, hs₀, rest⟩ := h
  have := het
  exact ⟨T', π, het,
    hs.mem_open ((BigFppfOver.toScheme B integerBase hZ).map π).isOpenMap.isOpen_range hs₀, rest⟩

/-- **Polarized charts push forward along étale morphisms of families.** -/
theorem HasPolarizedChartAt.of_hom {X Y : CurveFamily B hZ} (g : Y ⟶ X)
    (hg : Etale ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap))
    {y : (BigFppfOver.toScheme B integerBase hZ).obj Y.base} (h : HasPolarizedChartAt Y y) :
    HasPolarizedChartAt X ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap y) := by
  obtain ⟨T', π, het, ⟨u, rfl⟩, Z, p, q, hpb, L, hL, hamp⟩ := h
  refine ⟨T', π ≫ g.baseMap, ?_, ⟨u, ?_⟩, Z, p ≫ g.totalMap, q, ?_, L, hL, hamp⟩
  · rw [Functor.map_comp]
    have := het
    have := hg
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply]
  · rw [schemeSpaceMap_comp]
    exact hpb.paste_horiz g.cartesian

/-- **Polarized charts pull back along morphisms of families**: the base change of a polarized
chart is one, relative ampleness being stable under base change (Stacks 0893). -/
theorem HasPolarizedChartAt.of_hom_target {X X' : CurveFamily B hZ} (g : X ⟶ X')
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base}
    (h : HasPolarizedChartAt X' ((BigFppfOver.toScheme B integerBase hZ).map g.baseMap s)) :
    HasPolarizedChartAt X s := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨U', φ', het, ⟨u, hu⟩, Z', q', p', hpb, L', hL', hamp⟩ := h
  obtain ⟨w, hw⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq g.baseMap φ'
    (y := s) (z := u) hu.symm
  have hpbU := IsPullback.of_hasPullback g.baseMap φ'
  have hpbZ := IsPullback.of_hasPullback p' (pullback.snd g.baseMap φ')
  have hbot : schemeSpaceMap (pullback.snd g.baseMap φ') ≫ schemeSpaceMap φ' =
      schemeSpaceMap (pullback.fst g.baseMap φ') ≫ schemeSpaceMap g.baseMap := by
    rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, pullback.condition]
  have houter := (isPullback_schemeSpaceMap hpbZ).paste_horiz hpb
  let p : schemeSpace (pullback p' (pullback.snd g.baseMap φ')) ⟶ X.total :=
    g.cartesian.lift (schemeSpaceMap (pullback.fst p' (pullback.snd g.baseMap φ')) ≫ q')
      (schemeSpaceMap (pullback.snd p' (pullback.snd g.baseMap φ')) ≫
        schemeSpaceMap (pullback.fst g.baseMap φ'))
      (by rw [houter.w, hbot, Category.assoc])
  have := hL'
  refine ⟨pullback g.baseMap φ', pullback.fst g.baseMap φ', ?_, ⟨w, hw⟩,
    pullback p' (pullback.snd g.baseMap φ'), p, pullback.snd p' (pullback.snd g.baseMap φ'), ?_,
    pullbackModule (T.map (pullback.fst p' (pullback.snd g.baseMap φ'))) L', inferInstance,
    Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback (hpbZ.map T) L' hamp⟩
  · have := het
    exact MorphismProperty.of_isPullback (hpbU.map T).flip het
  · refine IsPullback.of_right ?_ (g.cartesian.lift_snd _ _ _) g.cartesian
    rw [g.cartesian.lift_fst, ← hbot]
    exact houter

/-- **Packaging a polarization along an open immersion into the base.** Let `X` have
representable total space `Z ⟶ S`. If `j : T ⟶ S` is an open immersion with `s` in its image
such that every scheme-theoretic base change of `Z ⟶ S` along `j` carries an invertible module
ample relative to its structure morphism, then `X` has a polarized chart at `s`. -/
theorem hasPolarizedChartAt_of_isOpenImmersion (X : CurveFamily B hZ)
    (hX : X.total.obj.IsRepresentable) {Tsch : Scheme.{u}}
    (j : Tsch ⟶ (BigFppfOver.toScheme B integerBase hZ).obj X.base) [IsOpenImmersion j]
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (hs : s ∈ Set.range j)
    (h : ∀ (Zt : Scheme.{u})
      (p : Zt ⟶ (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite hX))
      (g : Zt ⟶ Tsch),
      IsPullback p g ((BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase hX)) j →
      ∃ (L : Zt.Modules) (_ : IsInvertibleModule Zt L),
        Stacks.RelativeAmple.IsRelativelyAmple g L) :
    HasPolarizedChartAt X s := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let T' : BigFppfOver B integerBase hZ :=
    Over.mk (⟨j ≫ X.base.hom.hom⟩ :
      B.obj (Scheme.size_lt_of_isOpenImmersion j X.base.left.property) ⟶ B.obj hZ)
  let π : T' ⟶ X.base := Over.homMk ⟨j⟩ rfl
  let fZ := CurveFamily.totalSiteToBase hX
  let e : schemeSpace (CurveFamily.totalSite hX) ≅ X.total :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (CurveFamily.totalSiteIso hX)
  have he : e.hom ≫ X.toBase = schemeSpaceMap fZ ≫ 𝟙 _ := by
    rw [Category.comp_id]
    exact ObjectProperty.hom_ext _ (CurveFamily.yoneda_map_totalSiteToBase hX).symm
  have hsite := IsPullback.of_hasPullback fZ π
  have hsq : IsPullback (schemeSpaceMap (pullback.fst fZ π) ≫ e.hom)
      (schemeSpaceMap (pullback.snd fZ π)) X.toBase (schemeSpaceMap π) := by
    have h₂ : IsPullback e.hom (schemeSpaceMap fZ) X.toBase (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨he⟩
    simpa using (isPullback_schemeSpaceMap hsite).paste_horiz h₂
  obtain ⟨L, hL, hamp⟩ := h _ _ _ (hsite.map T)
  exact ⟨T', π, inferInstanceAs (Etale j), hs, _, _, _, hsq, L, hL, hamp⟩

/-! ### The polarized chart at a closed point -/

/-- **A divisor ample on a closed fibre polarizes a family with representable total space near
the fibre.** Let `Y` be a family of curves over a locally Noetherian base whose total space is a
scheme, `t` a closed point of the base given by a closed immersion from the spectrum of a field
with fibre `V`, and `D` a relative effective Cartier divisor of `Y` whose fibre is an effective
Cartier divisor `E` of `V` with `𝒪_V(E)` ample. Then `Y` has a polarized chart at `t`.

The closed subspace `D` of the represented total space `Z` is a closed subscheme of `Z`, flat
over the base, whose inverse image in `V` is `E`;
`AlgebraicGeometry.C1590Private.exists_isRelativelyAmple_near_closedPoint` polarizes `Z` over an
open neighbourhood of `t`, and `hasPolarizedChartAt_of_isOpenImmersion` packages it. -/
theorem hasPolarizedChartAt_of_isRelativeEffectiveCartierDivisor (Y : CurveFamily B hZ)
    (hY : Y.total.obj.IsRepresentable)
    (hYn : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj Y.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj)
    (hPci : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ Y.total.obj)
    (hq : IsPullback q (yoneda.map v) Y.toBase.hom (yonedaEquiv.symm P.value))
    (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj)
    (hD : Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (hDE : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1)
    (hE : IsAmpleDivisor ((BigFppfOver.toScheme B integerBase hZ).obj V) E) :
    HasPolarizedChartAt Y ((BigFppfOver.toScheme B integerBase hZ).map P.value
      (IsLocalRing.closedPoint P.carrier)) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let Zs := CurveFamily.totalSite hY
  let fZ := CurveFamily.totalSiteToBase hY
  let eY := CurveFamily.totalSiteIso hY
  -- the scheme properties of the total space
  have hid : schemeSpaceMap (𝟙 Y.base) = 𝟙 (schemeSpace Y.base) :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  let e : schemeSpace Zs ≅ Y.total := (ObjectProperty.fullyFaithfulι _).preimageIso eY
  have hsq₀ : IsPullback e.hom (schemeSpaceMap fZ) Y.toBase (schemeSpaceMap (𝟙 Y.base)) := by
    have : IsIso (schemeSpaceMap (𝟙 Y.base)) := by rw [hid]; infer_instance
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    apply ObjectProperty.hom_ext
    rw [hid, Category.comp_id]
    exact (CurveFamily.yoneda_map_totalSiteToBase hY).symm
  have : IsProper (T.map fZ) := Y.isProper_toScheme_map_of_isPullback_schemeSpaceMap hsq₀
  have : Flat (T.map fZ) := Y.flat_toScheme_map_of_isPullback hsq₀
  have : LocallyOfFinitePresentation (T.map fZ) :=
    Y.locallyOfFinitePresentation_toScheme_map_of_isPullback hsq₀
  have := hYn
  have : IsLocallyNoetherian (T.obj Zs) := LocallyOfFiniteType.isLocallyNoetherian (T.map fZ)
  -- the divisor as a closed subscheme of the total space
  let D' : Space.ClosedSubspaces B integerBase hZ (yoneda.obj Zs) :=
    ⟨D.1.preimage eY.hom, Space.isClosedSubspace_preimage B integerBase hZ eY.hom D.1 Y.total.2
      (isAlgebraicSpace_yoneda B integerBase hZ Zs) D.2⟩
  obtain ⟨R, j, hj, hrange, hker⟩ := Space.exists_closedImmersion_range_eq B integerBase hZ Zs D'
  set I := Space.schemeSpaceIdeal B integerBase hZ Zs D' with hIdef
  -- its flatness over the base
  have hpre := Subfunctor.isPullback_preimage eY.hom D.1
  have : IsIso (D.1.fromPreimage eY.hom) := hpre.isIso_fst_of_isIso
  have hflat₁ : Space.IsFlat B integerBase hZ
      ((D.1.preimage eY.hom).ι ≫ eY.hom ≫ Y.toBase.hom) := by
    have h := Space.holdsOnEveryEtaleChart_precomp_iso' B integerBase hZ _
      (asIso (D.1.fromPreimage eY.hom)) _ hD.2
    rw [← Category.assoc, ← hpre.w, Category.assoc]
    exact h
  have hrange' : Subfunctor.range (yoneda.map j) = D.1.preimage eY.hom := hrange
  rw [← hrange'] at hflat₁
  have hflat₂ : Space.IsFlat B integerBase hZ (yoneda.map j ≫ eY.hom ≫ Y.toBase.hom) := by
    have h := Space.holdsOnEveryEtaleChart_precomp_iso' B integerBase hZ _
      (Space.rangeIsoPresheaf B integerBase hZ j hj) _ hflat₁
    rw [← Subfunctor.toRange_ι (yoneda.map j), Category.assoc]
    exact h
  have := hj
  have : Flat (I.subschemeι ≫ T.map fZ) := by
    have h₃ : Flat (T.map j ≫ T.map fZ) := by
      rw [← Functor.map_comp]
      exact Space.flat_of_isFlat_yoneda B integerBase hZ _ _ _
        (by rw [Functor.map_comp, CurveFamily.yoneda_map_totalSiteToBase]; exact hflat₂)
    rw [← hker]
    have h₄ : (T.map j).ker.subschemeι ≫ T.map fZ =
        inv (T.map j).toImage ≫ (T.map j ≫ T.map fZ) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι]
    rw [h₄]
    infer_instance
  -- the fibre
  let qV : V ⟶ Zs := yoneda.preimage (q ≫ eY.inv)
  have hqV : yoneda.map qV = q ≫ eY.inv := yoneda.map_preimage _
  have hcomap : I.comap (T.map qV) = E := by
    rw [hIdef, ← Space.schemeSpaceIdeal_eq_comap_of_preimage_eq B integerBase hZ Zs qV D'
      (Space.closedSubspaceOfIdeal V E) ?_]
    · exact schemeSpaceIdeal_closedSubspaceOfIdeal B integerBase hZ V E
    · rw [← hDE, hqV]
      show _ = (D.1.preimage eY.hom).preimage (q ≫ eY.inv)
      rw [← Subfunctor.preimage_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [yonedaEquiv_symm_value] at hq
  have hsqY : IsPullback (yoneda.map qV) (yoneda.map v) (yoneda.map fZ)
      (yoneda.map (show P.siteObject ⟶ Y.base from P.value)) := by
    rw [hqV, CurveFamily.yoneda_map_totalSiteToBase]
    exact hq.of_iso (Iso.refl _) eY.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Iso.symm_hom]
          exact (Category.comp_id Y.toBase.hom).trans (Iso.inv_hom_id_assoc eY _).symm)
      (by simp only [Iso.refl_hom, Category.id_comp]
          exact Category.comp_id (yoneda.map (show P.siteObject ⟶ Y.base from P.value)))
  have hsite : IsPullback qV v fZ (show P.siteObject ⟶ Y.base from P.value) :=
    IsPullback.of_map yoneda
      (yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact hsqY.w)) hsqY
  -- the polarization
  obtain ⟨hEc, hEa⟩ := hE
  have : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (T.map qV)) :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_eq hcomap
  have := hPci
  obtain ⟨Tsch, jsch, hjsch, hmem, hpol⟩ :=
    exists_isRelativelyAmple_near_closedPoint (T.map fZ) I
      (K := P.carrier) (T.map P.value) (T.map qV) (T.map v) (hsite.map T)
      (isAmple_divisorSheaf_of_eq hcomap.symm hEa)
  have := hjsch
  exact hasPolarizedChartAt_of_isOpenImmersion Y hY jsch _ hmem hpol

/-! ### The reductions -/

/-- The inverse image of a relative effective Cartier divisor along an étale morphism of families
is one, and its inverse image along `q'` is that of the divisor along `q' ≫ φ`. -/
private theorem exists_isRelativeEffectiveCartierDivisor_preimage_eq {Y Y' : CurveFamily B hZ}
    (φ : Y ⟶ Y') (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap))
    (D : Space.ClosedSubspaces B integerBase hZ Y'.total.obj)
    (hD : Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y'.toBase D)
    {V : BigFppfOver B integerBase hZ} (q' : yoneda.obj V ⟶ Y.total.obj)
    (q : yoneda.obj V ⟶ Y'.total.obj) (hq : q' ≫ φ.totalMap.hom = q)
    {F : Subfunctor (yoneda.obj V)} (hF : D.1.preimage q = F) :
    ∃ D' : Space.ClosedSubspaces B integerBase hZ Y.total.obj,
      Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D' ∧
        D'.1.preimage q' = F :=
  ⟨⟨D.1.preimage φ.totalMap.hom, Space.isClosedSubspace_preimage B integerBase hZ
      φ.totalMap.hom D.1 Y'.total.2 Y.total.2 D.2⟩,
    isRelativeEffectiveCartierDivisor_preimage_totalMap φ hφ D hD, by
      change (D.1.preimage φ.totalMap.hom).preimage q' = F
      rw [← Subfunctor.preimage_comp, hq, hF]⟩

/-- **Reduction to an affine base**: restrict to an affine open neighbourhood of the point, an
open immersion being étale. -/
theorem hasPolarizedChartAt_of_isAffine
    (h : ∀ X : CurveFamily B hZ, IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
      ∀ s, HasPolarizedChartAt X s)
    (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    HasPolarizedChartAt X s := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, -⟩ :=
    ((BigFppfOver.toScheme B integerBase hZ).obj X.base).isBasis_affineOpens
      |>.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let Wo : BigFppfOver B integerBase hZ :=
    Over.mk (⟨Scheme.Opens.ι W ≫ X.base.hom.hom⟩ :
      B.obj (Scheme.size_lt_of_isOpenImmersion (Scheme.Opens.ι W) X.base.left.property) ⟶ B.obj hZ)
  let j : Wo ⟶ X.base := Over.homMk ⟨Scheme.Opens.ι W⟩ rfl
  have hsq := IsPullback.of_hasPullback X.toBase (schemeSpaceMap j)
  have hj : Etale ((BigFppfOver.toScheme B integerBase hZ).map j) :=
    inferInstanceAs (Etale (Scheme.Opens.ι W))
  exact (h (curveFamilyOfIsPullback X j _ _ hsq) hW ⟨s, hsW⟩).of_hom
    (curveFamilyOfIsPullbackHom X j _ _ hsq) hj

/-- **Reduction to a Noetherian affine base** (Stacks 0D55): a family over an affine base is the
base change of a family over a stage of the Noetherian approximation of the base, whose polarized
charts pull back. -/
theorem hasPolarizedChartAt_of_isNoetherian
    (h : ∀ X : CurveFamily B hZ,
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base) → ∀ s,
      HasPolarizedChartAt X s)
    (X : CurveFamily B hZ) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : HasPolarizedChartAt X s := by
  obtain ⟨i, ⟨Y, hY⟩, δ, -⟩ := descentObj_curvesProjectionOver
    (affineSiteStageDiagram B hZ X.base) (isLimit_affineSiteStageCone B hZ X.base)
    (Functor.Fiber.mk (p := curvesProjectionOver B hZ) (a := X) rfl)
  change Y.base = ((affineSiteStageDiagram B hZ X.base).obj i).1 at hY
  have hYa : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) := by
    rw [hY]
    exact ((affineSiteStageDiagram B hZ X.base).obj i).2
  have hYn : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) := by
    rw [hY]
    exact isNoetherian_affineSiteStageDiagram_obj B hZ X.base i
  exact (h Y hYa hYn _).of_hom_target δ

/-- **Reduction to closed points**: on a quasi-compact base a point specializes to a closed point,
and the polarized chart locus is closed under generization. -/
theorem hasPolarizedChartAt_of_isClosed_singleton (X : CurveFamily B hZ)
    [CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    (h : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base, IsClosed {s} →
      HasPolarizedChartAt X s)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : HasPolarizedChartAt X s := by
  obtain ⟨s₀, hs₀, hcl⟩ := (isClosed_closure (s := {s})).exists_closed_singleton
    ⟨s, subset_closure rfl⟩
  exact (h s₀ hcl).of_specializes (specializes_iff_mem_closure.2 hs₀)

variable (B hZ) in
/-- **A family of curves over an affine Noetherian base has a polarized chart at a closed point.**
The fibre `V` carries two good divisors `E₁, E₂` with `𝒪_V(E₁)` ample (P1 with ampleness); P2
lifts `E₁` over an étale `Y₁ ⟶ X` and `E₂` over an étale `Y₂ ⟶ Y₁`; P3 makes `Y₂` a scheme over
an open neighbourhood `U'` of the point; and on the base change `Y₃` of `Y₂` to `U'` the pulled
back lift of `E₁` polarizes the family near the fibre
(`hasPolarizedChartAt_of_isRelativeEffectiveCartierDivisor`). -/
theorem hasPolarizedChartAt_of_isClosed (X : CurveFamily B hZ)
    (hX : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (hXn : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (hs : IsClosed {s}) :
    HasPolarizedChartAt X s := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have hP3 : SchemeNearFibreOfGoodDivisors B hZ (IsGoodFibreDivisor B hZ) :=
    schemeNearFibreOfGoodDivisors B hZ
  have hP2 : DivisorLiftAtClosedFibre B hZ := divisorLiftReduction divisorLiftAtClosedFibreLocal
  let P := X.residueFieldPoint s
  have hPci : IsClosedImmersion (T.map P.value) :=
    isClosed_singleton_iff_isClosedImmersion.1 hs
  obtain ⟨V, v, q, hq⟩ := exists_presentation_of_fieldValuedPoint X P
  obtain ⟨E₁, E₂, hE₁, hE₂, hf₁, hf₂, hdisj, hg₁, hg₂⟩ :=
    fibreGoodDivisorPair_isAmple B hZ X P hPci V v q hq
  -- lift `E₁`
  obtain ⟨Y₁, φ₁, t₁, q₁, D₁, het₁, ht₁, hci₁, hpb₁, hq₁, haff₁, hrel₁, hpre₁⟩ :=
    hP2 X hX P hPci V v q hq E₁ hE₁ hf₁
  let P₁ : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y₁.base).obj :=
    { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t₁ }
  have hpb₁' : IsPullback q₁ (yoneda.map v) Y₁.toBase.hom (yonedaEquiv.symm P₁.value) := by
    rw [yonedaEquiv_symm_value P₁]
    exact hpb₁
  -- lift `E₂` over `Y₁`
  obtain ⟨Y₂, φ₂, t₂, q₂, D₂, het₂, ht₂, hci₂, hpb₂, hq₂, haff₂, hrel₂, hpre₂⟩ :=
    hP2 Y₁ haff₁ P₁ hci₁ V v q₁ hpb₁' E₂ hE₂ hf₂
  let P₂ : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y₂.base).obj :=
    { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t₂ }
  have hpb₂' : IsPullback q₂ (yoneda.map v) Y₂.toBase.hom (yonedaEquiv.symm P₂.value) := by
    rw [yonedaEquiv_symm_value P₂]
    exact hpb₂
  -- the first lift, pulled back to `Y₂`
  obtain ⟨D₁', hrel₁', hpre₁'⟩ :=
    exists_isRelativeEffectiveCartierDivisor_preimage_eq φ₂ het₂ D₁ hrel₁ q₂ q₁ hq₂ hpre₁
  -- the base of `Y₂` is locally Noetherian
  have := het₁
  have := het₂
  have := hXn
  have hn₂ : IsLocallyNoetherian (T.obj Y₂.base) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map φ₂.baseMap ≫ T.map φ₁.baseMap)
  obtain ⟨U', j, hj, ⟨t, ht⟩, hrep⟩ := hP3 Y₂ haff₂ hn₂ P₂ hci₂ V v q₂ hpb₂' D₁' D₂ E₁ E₂
    hrel₁' hrel₂ hpre₁' hpre₂ hdisj hg₁.1 hg₂.1
  have htj : t ≫ j = t₂ := by
    apply yoneda.map_injective
    rw [ht, yonedaEquiv_symm_value]
  -- the base change `Y₃` of `Y₂` to `U'`, a family with representable total space
  have hsq := IsPullback.of_hasPullback Y₂.toBase (schemeSpaceMap j)
  let Y₃ := curveFamilyOfIsPullback Y₂ j _ _ hsq
  let ψ : Y₃ ⟶ Y₂ := curveFamilyOfIsPullbackHom Y₂ j _ _ hsq
  have h₃ : Y₃.total.obj.IsRepresentable := hrep Y₃ ψ (𝟙 _) (Category.id_comp _)
  have := hj
  have hjet : Etale (T.map ψ.baseMap) := inferInstanceAs (Etale (T.map j))
  have hn₃ : IsLocallyNoetherian (T.obj Y₃.base) :=
    @isLocallyNoetherian_of_isOpenImmersion _ _ (T.map j) hj hn₂
  -- the closed point of `Y₃`
  let P₃ : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y₃.base).obj :=
    { carrier := P.carrier, contained := P.contained, toBase := P.toBase, value := t }
  have : IsClosedImmersion (T.map t ≫ T.map j) := by
    rw [← Functor.map_comp, htj]
    exact hci₂
  have hci₃ : IsClosedImmersion (T.map P₃.value) := IsClosedImmersion.of_comp (T.map t) (T.map j)
  -- the fibre of `Y₃`
  have hpb₂A := isPullback_homMk_of_isPullback t₂ v q₂ hpb₂
  rw [← htj, schemeSpaceMap_comp] at hpb₂A
  let q₃ : schemeSpace V ⟶ Y₃.total := ψ.cartesian.lift (ObjectProperty.homMk q₂)
    (schemeSpaceMap v ≫ schemeSpaceMap t) (by rw [hpb₂A.w, Category.assoc]; rfl)
  have hq₃A : IsPullback q₃ (schemeSpaceMap v) Y₃.toBase (schemeSpaceMap t) :=
    IsPullback.of_right (by rw [ψ.cartesian.lift_fst]; exact hpb₂A) (ψ.cartesian.lift_snd _ _ _)
      ψ.cartesian
  have hq₃ : IsPullback q₃.hom (yoneda.map v) Y₃.toBase.hom (yonedaEquiv.symm P₃.value) := by
    rw [yonedaEquiv_symm_value P₃]
    exact AlgebraicSpaces.isPullback_hom B integerBase hZ hq₃A
  -- the first lift on `Y₃`
  obtain ⟨D₃, hrel₃, hpre₃⟩ := exists_isRelativeEffectiveCartierDivisor_preimage_eq ψ hjet D₁'
    hrel₁' q₃.hom q₂ (congrArg (fun k : schemeSpace V ⟶ Y₂.total => k.hom)
      (ψ.cartesian.lift_fst _ _ _)) hpre₁'
  have hc := hasPolarizedChartAt_of_isRelativeEffectiveCartierDivisor Y₃ h₃ hn₃ P₃ hci₃ V v
    q₃.hom hq₃ D₃ hrel₃ E₁ hpre₃ hg₁.2
  have hc' := ((hc.of_hom ψ hjet).of_hom φ₂ het₂).of_hom φ₁ het₁
  have hx : T.map (((t ≫ j) ≫ φ₂.baseMap) ≫ φ₁.baseMap) (IsLocalRing.closedPoint P.carrier) =
      s := by
    have ht₂' : t₂ ≫ φ₂.baseMap = t₁ := ht₂
    rw [htj, ht₂', ht₁]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [← hx]
  simp only [Functor.map_comp]
  exact hc'

variable (B hZ) in
/-- **Every family of curves has a polarized chart at every point**: through every point of the
base there is an étale morphism of the site over which the family is a scheme carrying a
relatively ample invertible module. -/
theorem hasPolarizedChartAt (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : HasPolarizedChartAt X s := by
  refine hasPolarizedChartAt_of_isAffine (fun X hX s => ?_) X s
  refine hasPolarizedChartAt_of_isNoetherian (fun Y hYa hYn s => ?_) X s
  exact hasPolarizedChartAt_of_isClosed_singleton Y
    (fun s hs => hasPolarizedChartAt_of_isClosed B hZ Y hYa inferInstance s hs) s

/-! ### Step C -/

variable (B hZ) in
/-- **Step C.** Every family of curves is smooth locally polarized: through every point of the
base there is a smooth (in practice étale) chart along which the family is a scheme carrying an
invertible module ample relative to the chart. With base's
`CurveFamily.exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized` this gives a
common étale neighbourhood over which finitely many families are H-projective schemes. -/
def CurvesSmoothLocallyPolarized : Prop :=
  ∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized

variable (B hZ) in
/-- **Every family of curves is smooth locally polarized** (the smoothness half of Stacks 0DQ0 for
a single family, unwound as in the proof of Stacks 0E6F): the polarized charts of
`hasPolarizedChartAt` are étale, hence smooth. -/
theorem curvesSmoothLocallyPolarized : CurvesSmoothLocallyPolarized B hZ := by
  intro X s
  obtain ⟨T', π, het, hs, Z, p, q, hsq, L, hL, hamp⟩ := hasPolarizedChartAt B hZ X s
  have := het
  exact ⟨T', π, inferInstance, hs, Z, p, q, hsq, L, hL, hamp⟩

end AlgebraicGeometry.C1590Private

end
