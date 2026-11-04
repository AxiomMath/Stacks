module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuasiFiniteChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartDoubleFibreQuasiDM

/-!
# The chart of Stacks 06MF at a finite type point of a quasi-DM algebraic stack

Let `𝒳` be an algebraic stack over `S` which is quasi-DM over `S` and let `x` be a finite type
point of `|𝒳|` (Stacks 06FY). This file constructs, as in the proof of Stacks 06MF, a scheme `Z`
of the site with a 1-morphism `Z ⟶ 𝒳` which is flat, locally of finite presentation and locally
quasi-finite in the sense of Stacks 04XB, and whose image on points contains `x`. The size of `Z`
is bounded in terms of that of one fixed smooth surjective scheme chart `U₀ ⟶ 𝒳`, uniformly in
`x`.

## Main results

* `exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_finiteTypePoint`:
  the chart of Stacks 06MF at a finite type point of a quasi-DM algebraic stack, with its
  size bounded by `2 ^ 2 ^ size U₀`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `𝒳` be an algebraic stack over `S` which is quasi-DM over `S`, let `a₀ : U₀ ⟶ 𝒳` be a
smooth surjective 1-morphism out of a scheme of the site, and let `x` be a finite type point of
`|𝒳|`. Then some scheme `Z` of the site of size at most `2 ^ 2 ^ size U₀` carries a 1-morphism
`Z ⟶ 𝒳` which is flat, locally of finite presentation, locally quasi-finite in the sense of
Stacks 04XB, and whose image on points contains `x`. -/
theorem exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_finiteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (U₀ : BigFppfOver B S hS) (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (ha₀sm : AlgebraicStacks.IsSmooth B S hS a₀) (ha₀surj : IsSurjective B S hS a₀)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
      AlgebraicStacks.IsFlat B S hS c ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c ∧
      IsLocallyQuasiFinite B S hS c.hom ∧
      x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
      ((BigFppfOver.toScheme B S hS).obj Z).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
          ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  classical
  obtain ⟨U, p, z, hpsmooth, hclosed, hpz, hUsize, -⟩ :=
    exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint.{u, w} B S hS 𝒳 U₀ a₀ ha₀sm ha₀surj
      x hx
  have hPfp : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS p p) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p
  have hprep : IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) p.hom
  obtain ⟨F, hF, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val
    (schemeStack.{u, w} B S hS U).val p.hom p.hom
    (twoFibreProductSquareAlgebraicStacks B S hS p p).underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS p p) hPfp)
    hprep (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  obtain ⟨R, cR, hcRsurj, hcRetale⟩ := hF.exists_atlas
  have hab := smooth_chartLeg B S hS U p (twoFibreProductSquareAlgebraicStacks B S hS p p)
    F eF R cR hF hcRetale hpsmooth hPfp
  have : Smooth ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (twoFibreProductSquareAlgebraicStacks B S hS p p).fst)) := hab.1
  have : Smooth ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)) := hab.2
  obtain ⟨r₀, har, hbr⟩ := exists_point_chartLeg_eq B S hS U p
    (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR hPfp hcRsurj
    (pointsHomeomorphScheme B S hS U z)
  obtain ⟨Zs, Ts, ιZ, jj, kk, t₀, hιmono, hjmono, hcomm, hkflat, hklfp, hksurj,
    hbflat, hblfp, hjt, hqfslice, Ws, jWs, jTs, hjWs, hjfac, hpbs⟩ :=
    exists_mono_flat_surjective_slice_of_smooth _ _ r₀
      (isIsolatedPoint_asFiber_chartLeg_of_isQuasiDM B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR h𝒳 hPfp
        (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS p hpsmooth) hF hcRetale r₀
        (har.trans hbr.symm) (by rw [hbr]; exact hclosed))
  have := hιmono
  have := hjmono
  have hZc : B.Contains Zs := BigFppfSite.contains_of_mono B ιZ U.left.2
  have hTc : B.Contains Ts := BigFppfSite.contains_of_mono B jj R.left.2
  set Zsite : BigFppfOver B S hS :=
    siteObject B S hS hZc (ιZ ≫ B.inclusion.map U.hom) with hZsite
  set Tsite : BigFppfOver B S hS :=
    siteObject B S hS hTc (jj ≫ B.inclusion.map R.hom) with hTsite
  set ιsite : Zsite ⟶ U := Over.homMk (ObjectProperty.homMk ιZ) rfl with hιsite
  set jsite : Tsite ⟶ R := Over.homMk (ObjectProperty.homMk jj) rfl with hjsite
  have hwk : (ObjectProperty.homMk kk : B.obj hTc ⟶ B.obj hZc) ≫ Zsite.hom = Tsite.hom := by
    refine ObjectProperty.hom_ext _ ?_
    show kk ≫ ιZ ≫ B.inclusion.map U.hom = jj ≫ B.inclusion.map R.hom
    rw [← Category.assoc, hcomm, Category.assoc]
    refine congrArg (fun m => jj ≫ m) ?_
    show B.inclusion.map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).fst).left ≫
      B.inclusion.map U.hom = B.inclusion.map R.hom
    rw [← B.inclusion.map_comp, Over.w]
  set ksite : Tsite ⟶ Zsite := Over.homMk (ObjectProperty.homMk kk) hwk with hksite
  have := hjWs
  have hWc : B.Contains Ws := BigFppfSite.contains_of_mono B jWs R.left.2
  set Wsite : BigFppfOver B S hS :=
    siteObject B S hS hWc (jWs ≫ B.inclusion.map R.hom) with hWsite
  set jWsite : Wsite ⟶ R := Over.homMk (ObjectProperty.homMk jWs) rfl with hjWsite
  have hwT : (ObjectProperty.homMk jTs : B.obj hTc ⟶ B.obj hWc) ≫ Wsite.hom = Tsite.hom := by
    refine ObjectProperty.hom_ext _ ?_
    show jTs ≫ jWs ≫ B.inclusion.map R.hom = jj ≫ B.inclusion.map R.hom
    rw [← Category.assoc, hjfac]
  set jTsite : Tsite ⟶ Wsite := Over.homMk (ObjectProperty.homMk jTs) hwT with hjTsite
  have hjsitefac : jTsite ≫ jWsite = jsite :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hjfac)
  have hcommsite : ksite ≫ ιsite = jsite ≫ chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (twoFibreProductSquareAlgebraicStacks B S hS p p).fst :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hcomm)
  obtain ⟨hcflat, hclfp⟩ := isFlat_and_isLocallyOfFinitePresentation_chartedSlice
    B S hS U p (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR hpsmooth
    Zsite Tsite ιsite jsite ksite hcommsite hkflat hklfp (fun ζ => hksurj ζ)
    (by
      show Flat (jj ≫ (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd))
      exact hbflat)
    (by
      show LocallyOfFinitePresentation
        (jj ≫ (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd))
      exact hblfp)
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  let := pointTopology B S hS (schemeFibredCategory B S hS Zsite)
  have hzs : pointsHomeomorphScheme B S hS Zsite
      ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) = kk t₀ :=
    (pointsHomeomorphScheme B S hS Zsite).apply_symm_apply _
  have hkey : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιsite)
      ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) = z := by
    refine (pointsHomeomorphScheme B S hS U).injective ?_
    rw [show AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιsite)
          ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) =
        pointsMap B S hS (schemeFibredCategory B S hS Zsite).val
          (schemeFibredCategory B S hS Zsite).property
          (schemeFibredCategory B S hS U).property
          (schemeFibredCategoryMap B S hS ιsite).hom
          ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) from rfl,
      pointsHomeomorphScheme_naturality, Homeomorph.apply_symm_apply]
    have hc : ιZ (kk t₀) = (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).fst) (jj t₀) := by
      show (kk ≫ ιZ) t₀ = _
      rw [hcomm]
      rfl
    show ιZ (kk t₀) = _
    rw [hc, hjt, har]
  have hy : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιsite ≫ p)
      ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) = x := by
    rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hkey]
    exact hpz
  have hbb : jTsite ≫ jWsite ≫ chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd =
      jsite ≫ chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd := by
    rw [← Category.assoc, hjsitefac]
  have hbTlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (jTsite ≫ jWsite ≫ chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)) := by
    rw [hbb, Functor.map_comp]
    exact hblfp
  have := hbTlfp
  have hqfpt : quasiFiniteAt ((BigFppfOver.toScheme B S hS).map
      (jTsite ≫ jWsite ≫ chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)) t₀ := by
    rw [hbb, Functor.map_comp]
    exact hqfslice (isClosed_asFiber_chartLeg_of_isQuasiDM B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR h𝒳 hPfp
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS p hpsmooth) hF hcRetale r₀
      (har.trans hbr.symm) (by rw [hbr]; exact hclosed))
  have hpbsite : IsPullback jTsite ksite (jWsite ≫ chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (twoFibreProductSquareAlgebraicStacks B S hS p p).fst) ιsite := by
    refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
    rw [Functor.map_comp]
    exact hpbs
  have hZsize : ((BigFppfOver.toScheme B S hS).obj Zsite).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj U₀).size := by
    refine (Scheme.size_le_of_mono ιZ).trans (max_le ?_ ?_)
    · exact power_le_power_left two_ne_zero
        (((BigFppfOver.toScheme B S hS).obj U).mk_le_two_pow_size.trans
          (power_le_power_left two_ne_zero hUsize))
    · exact hUsize.trans ((Cardinal.cantor _).le.trans (Cardinal.cantor _).le)
  obtain ⟨Z', c', hflat, hlfp, hlqf, hrange, hsize⟩ :=
    exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice.{u, w}
      B S hS U p hpsmooth F eF R cR hcRetale Zsite ιsite hcflat hclfp (kk t₀)
      ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) hzs x hy Wsite Tsite jWsite jTsite
      ksite (inferInstanceAs (Etale jWs)) hpbsite inferInstance t₀ rfl hqfpt
  exact ⟨Z', c', hflat, hlfp, hlqf, hrange, hsize.trans hZsize⟩

end AlgebraicGeometry.Stack

end
