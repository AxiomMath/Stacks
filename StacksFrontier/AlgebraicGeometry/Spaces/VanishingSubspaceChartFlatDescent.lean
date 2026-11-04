module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GlobalSectionSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringAffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Flatness of `V(f₁, …, f_r)` over the target, read off one affine étale chart

Let `X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site,
let `f₁, …, f_r` be global regular functions on `X` and let `V(f₁, …, f_r) ⊆ X` be the closed
subspace they cut out.  Let `U ⟶ X` be an étale chart with affine underlying scheme lying over
an étale chart `V ⟶ Y` of the target, through a morphism of the site `U ⟶ V`.

This file descends flatness over `Y` of the part of `V(f₁, …, f_r)` lying over the open
subspace of `X` swept out by `U` from flatness of a single morphism of schemes, the zero scheme
of the restricted functions over `V`, and obtains that flatness, on an affine Zariski open of a
chart, from regularity of the restricted functions on a fibre.

## Main results

* `AlgebraicGeometry.Space.unitSections_eval_openChart`: the value of a global regular function
  on the étale chart cut out by a Zariski open of a chart is the restriction of its value on
  that chart.
* `AlgebraicGeometry.Space.isFlat_preimage_vanishingSubfunctor_openSubspaceOfPoints`: if the zero
  scheme of the restricted functions on an affine étale chart `U` is flat over the chart `V` of
  the target, then `V(f₁, …, f_r) ∩ X' ⟶ Y` is flat, for `X'` the open subspace of `X` swept out
  by `U`.
* `AlgebraicGeometry.Space.exists_affineOpen_isFlat_preimage_vanishingSubfunctor`: the same
  conclusion for an affine Zariski open of a chart `U`, from regularity of the restricted
  functions in the local ring of the scheme-theoretic fibre of `U ⟶ V` at a point.

## References

* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The value of a global regular function on the étale chart cut out by a Zariski open `O` of a
chart `U` is the restriction to `O` of its value on `U`. -/
theorem unitSections_eval_openChart (X : AlgebraicSpaces B S hS)
    (a : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1) (O : (chartScheme U).Opens) :
    a.eval (op (openChart B S hS X.1 U O)) = O.ι.appTop (a.eval (op U)) := by
  rw [← toScheme_map_toOver_map_openChartInclusion B S hS X.1 U O]
  exact (a.property (openChartInclusion B S hS X.1 U O).op).symm

/-- Let `A ⟶ X` be an étale chart with affine underlying scheme lying over an étale chart
`V ⟶ Y` of the target through a morphism of the site `A ⟶ V`.  If the scheme-theoretic zero
scheme of the restrictions of `f₁, …, f_r` to `A` is flat over `V`, then
`V(f₁, …, f_r) ∩ X' ⟶ Y` is flat, where `X' ⊆ X` is the open subspace swept out by `A`. -/
theorem isFlat_preimage_vanishingSubfunctor_openSubspaceOfPoints
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (Vobj : BigFppfOver B S hS) (cY : yoneda.obj Vobj ⟶ Y.1)
    (hcY : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf cY)
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
    (gAV : (SmallEtale.toOver B S hS X.1).obj A ⟶ Vobj)
    (hcomm : yoneda.map gAV ≫ cY = A.obj.hom ≫ g)
    (hflat : _root_.AlgebraicGeometry.Flat
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.ofList (List.ofFn fun i => (f i).eval (op A)))).subschemeι ≫
          (BigFppfOver.toScheme B S hS).map gAV)) :
    IsFlat B S hS
      (((vanishingSubfunctor B S hS X f).preimage
          (openSubspaceOfPoints B S hS X.1
            (Set.range (pointsMap B S hS
              (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom))).ι).ι ≫
        (openSubspaceOfPoints B S hS X.1
            (Set.range (pointsMap B S hS
              (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom))).ι ≫ g) := by
  classical
  obtain ⟨hWopen, hlEt, hlSurjPt, hlSurj⟩ :=
    isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda B S hS X.2
      ((SmallEtale.toOver B S hS X.1).obj A) A.obj.hom A.property
  obtain ⟨Z, hZeq, hZe⟩ := exists_closedSubspace_iso_zeroScheme_chartBaseChange B S hS X f
  obtain ⟨e, he⟩ := hZe A hA
  rw [hZeq]
  set W := openSubspaceOfPoints B S hS X.1
    (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom)) with hWdef
  set ℓ := Subfunctor.lift A.obj.hom
    (range_le_openSubspaceOfPoints_range_pointsMap A.obj.hom) with hℓdef
  have hℓι : ℓ ≫ W.ι = A.obj.hom := Subfunctor.lift_ι _ _
  have hright : IsPullback (Z.1.fromPreimage W.ι) (Z.1.preimage W.ι).ι Z.1.ι W.ι :=
    Subfunctor.isPullback_preimage W.ι Z.1
  have hpb := Z.2.2.rep.isPullback A.obj.hom
  have hQ := isClosedSubspace_preimage B S hS W.ι Z.1 X.2 hWopen.1 Z.2
  set p := hright.lift (Z.2.2.rep.fst A.obj.hom)
    (yoneda.map (Z.2.2.rep.snd A.obj.hom) ≫ ℓ)
    (by rw [Category.assoc, hℓι]; exact hpb.w) with hpdef
  have hpfst : p ≫ Z.1.fromPreimage W.ι = Z.2.2.rep.fst A.obj.hom := hright.lift_fst _ _ _
  have hpsnd : p ≫ (Z.1.preimage W.ι).ι = yoneda.map (Z.2.2.rep.snd A.obj.hom) ≫ ℓ :=
    hright.lift_snd _ _ _
  have houter : IsPullback (p ≫ Z.1.fromPreimage W.ι)
      (yoneda.map (Z.2.2.rep.snd A.obj.hom)) Z.1.ι (ℓ ≫ W.ι) := by
    rwa [hpfst, hℓι]
  have hleft : IsPullback p (yoneda.map (Z.2.2.rep.snd A.obj.hom))
      (Z.1.preimage W.ι).ι ℓ :=
    IsPullback.of_right houter hpsnd hright
  have hbc := fun (P : MorphismProperty Scheme.{u}) =>
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (P.inverseImage (BigFppfOver.toScheme B S hS))).of_isPullback hleft.flip
  have hpEt := hbc _ hlEt
  have hpSurjP := hbc _ hlSurj
  have hpSurj : IsSurjective B S hS p :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hQ.1 _ p).mp hpSurjP
  have htfae := (isFlat_tfae B S hS hQ.1 Y.2
    ((Z.1.preimage W.ι).ι ≫ W.ι ≫ g)).out 8 1
  refine htfae.mp
    ⟨Z.2.2.rep.pullback A.obj.hom, Vobj, p, cY, Z.2.2.rep.snd A.obj.hom ≫ gAV,
      isEtale_of_presheaf_etale B S hS hpEt, isEtale_of_presheaf_etale B S hS hcY,
      hpSurj, ?_, ?_⟩
  · rw [← Category.assoc, hpsnd, Category.assoc,
      ← Category.assoc ℓ W.ι g, hℓι, ← hcomm, Functor.map_comp, Category.assoc]
  · refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget _).mpr ?_
    rw [Functor.map_comp]
    show _root_.AlgebraicGeometry.Flat
      (chartBaseChangeHom B S hS X Z A ≫ (BigFppfOver.toScheme B S hS).map gAV)
    rw [← he, Category.assoc]
    infer_instance

/-- Let `U ⟶ X` be an étale chart lying over an étale chart `V ⟶ Y` of the target through a
morphism of the site whose underlying morphism of schemes `U ⟶ V` is locally of finite
presentation, let `x` be a point of `U` at which that morphism is flat, and suppose the
restrictions of `f₁, …, f_r` to the scheme-theoretic fibre of `U ⟶ V` through `x` are a regular
sequence in its local ring at `x`.

Then an affine Zariski open `O` of `U` containing `x` has the property that
`V(f₁, …, f_r) ∩ X' ⟶ Y` is flat, where `X' ⊆ X` is the open subspace swept out by the étale
chart `O ⟶ X`. -/
theorem exists_affineOpen_isFlat_preimage_vanishingSubfunctor
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (Vobj : BigFppfOver B S hS) (cY : yoneda.obj Vobj ⟶ Y.1)
    (hcY : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf cY)
    (Uc : SmallEtale B S hS X.1)
    (gUV : (SmallEtale.toOver B S hS X.1).obj Uc ⟶ Vobj)
    (hcomm : yoneda.map gUV ≫ cY = Uc.obj.hom ≫ g)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map gUV)]
    (x : chartScheme Uc)
    (y : (((BigFppfOver.toScheme B S hS).map gUV).fiber
      (((BigFppfOver.toScheme B S hS).map gUV) x)))
    (hy : ((BigFppfOver.toScheme B S hS).map gUV).fiberι
      (((BigFppfOver.toScheme B S hS).map gUV) x) y = x)
    (hflatAt : _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map gUV).toLRSHom.toShHom x)
    (hreg : RingTheory.Sequence.IsRegular
      ((((BigFppfOver.toScheme B S hS).map gUV).fiber
        (((BigFppfOver.toScheme B S hS).map gUV) x)).presheaf.stalk y)
      (List.ofFn fun i : Fin r =>
        (((BigFppfOver.toScheme B S hS).map gUV).fiber
          (((BigFppfOver.toScheme B S hS).map gUV) x)).presheaf.germ ⊤ y trivial
          ((((BigFppfOver.toScheme B S hS).map gUV).fiberι
            (((BigFppfOver.toScheme B S hS).map gUV) x)).appTop ((f i).eval (op Uc))))) :
    ∃ O : (chartScheme Uc).affineOpens, x ∈ O.1 ∧
      IsFlat B S hS
        (((vanishingSubfunctor B S hS X f).preimage
            (openSubspaceOfPoints B S hS X.1
              (Set.range (pointsMap B S hS
                (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
                  (openChart B S hS X.1 Uc O.1)))
                (openChart B S hS X.1 Uc O.1).obj.hom))).ι).ι ≫
          (openSubspaceOfPoints B S hS X.1
              (Set.range (pointsMap B S hS
                (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
                  (openChart B S hS X.1 Uc O.1)))
                (openChart B S hS X.1 Uc O.1).obj.hom))).ι ≫ g) := by
  obtain ⟨O, hxO, hflat, -⟩ :=
    Stacks.AlgebraicGeometry.exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber_germ
      ((BigFppfOver.toScheme B S hS).map gUV) x y hy
      (fun i => (f i).eval (op Uc)) hflatAt hreg
  refine ⟨O, hxO, isFlat_preimage_vanishingSubfunctor_openSubspaceOfPoints B S hS X Y g f
    Vobj cY hcY (openChart B S hS X.1 Uc O.1) O.2 (openSubHom _ O.1 ≫ gUV) ?_ ?_⟩
  · show yoneda.map (openSubHom _ O.1 ≫ gUV) ≫ cY =
      (yoneda.map (openSubHom _ O.1) ≫ Uc.obj.hom) ≫ g
    rw [Functor.map_comp, Category.assoc, hcomm, Category.assoc]
  · have eq2 : (List.ofFn fun i : Fin r => (f i).eval (op (openChart B S hS X.1 Uc O.1))) =
        List.ofFn fun i : Fin r => O.1.ι.appTop ((f i).eval (op Uc)) :=
      congrArg List.ofFn (funext fun i => unitSections_eval_openChart B S hS X (f i) Uc O.1)
    have eq1 : (BigFppfOver.toScheme B S hS).map
        (openSubHom ((SmallEtale.toOver B S hS X.1).obj Uc) O.1 ≫ gUV) =
        O.1.ι ≫ (BigFppfOver.toScheme B S hS).map gUV := by
      rw [Functor.map_comp, toScheme_map_openSubHom]
      rfl
    exact (congrArg₂ (fun (l : List Γ(chartScheme (openChart B S hS X.1 Uc O.1), ⊤))
      (m : chartScheme (openChart B S hS X.1 Uc O.1) ⟶
        (BigFppfOver.toScheme B S hS).obj Vobj) =>
      _root_.AlgebraicGeometry.Flat
        ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList l)).subschemeι ≫ m))
      eq2 eq1).mpr hflat

end AlgebraicGeometry.Space

end
