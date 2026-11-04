module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPointsTopology
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingFamily
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOpenDense
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic

/-!
# `|Curves^{smooth}|` is open and dense in `|Curves^{lci+}|` (Stacks 0E86)

Stacks 0E86 says that the inclusion `|Curves^{smooth}| ⊂ |Curves^{lci+}|` is that of an open dense
subset. Both are read in the space `|Curves|` of points of the stack of curves
(`AlgebraicGeometry.CurvesPoints`, with the topology of Stacks 04Y8), as the sets of points
represented by a field-valued point whose family of curves is smooth, respectively lies in
`Curves^{lci+}` (`AlgebraicGeometry.curvesPointSet`).

* **Inclusion.** A smooth family of curves is a local complete intersection morphism with empty
  singular locus, so it lies in `Curves^{lci+}`.
* **Openness.** `|Curves^{smooth}|` is open in `|Curves|`, smoothness satisfying condition (o) of
  Stacks 0E0E, hence open in `|Curves^{lci+}|`.
* **Density.** A point of `|Curves^{lci+}|` is classified by a proper scheme `X` of dimension at
  most one over a field `k`, which by Stacks 0DZX, part (3), is a local complete intersection over
  `k` smooth except at finitely many points. Its smoothing `Y ⟶ Spec k⟦t⟧` (Stacks 0E7Y) is a
  family of curves with smooth generic fibre and special fibre `X`, and the generic point of
  `Spec k⟦t⟧` specializes to the closed point, so the point of the generic fibre, which lies in
  `|Curves^{smooth}|`, specializes to the point of `X`.

## Main results

* `AlgebraicGeometry.mem_closure_curvesPointSet_isSmoothFamily_of_mem_lciPlus`: every point of
  `|Curves^{lci+}|` lies in the closure of `|Curves^{smooth}|`.
* `AlgebraicGeometry.curvesPointSet_smooth_isOpen_dense_in_lciPlus`: **Stacks 0E86**.

## References

* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Every point of `|Curves^{lci+}|` lies in the closure of `|Curves^{smooth}|`.** It is
classified by a proper scheme `X` of dimension at most one over a field `k`, a local complete
intersection over `k` smooth except at finitely many points; a smoothing `Y ⟶ Spec k⟦t⟧` of `X`
(Stacks 0E7Y) has smooth generic fibre, and the point of the generic fibre specializes to that of
`X`. -/
theorem mem_closure_curvesPointSet_isSmoothFamily_of_mem_lciPlus {x : CurvesPoints B hZ}
    (hx : x ∈ curvesPointSet B hZ (IsLciPlusFamily B hZ)) :
    x ∈ closure (curvesPointSet B hZ (IsSmoothFamily B hZ)) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨k, _, hk, X, _, hdim, φ, -, hcls⟩ := exists_curveFamilyOfScheme_hom p
  rw [← hcls]
  obtain ⟨hlci, hfin⟩ := (isLciPlusFamily_curveFamilyOfScheme_iff B hZ k hk X hdim).1
    ((isOpenCurvesLocus_lciPlus B hZ).prop_of_hom φ hp)
  -- the smoothing of Stacks 0E7Y
  have hsyn : Syntomic X.hom :=
    (syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism X.hom).2 ⟨inferInstance, hlci⟩
  obtain ⟨Y, f, hflat, hproj, hsm, e, he⟩ :=
    Deformation.Examples.Smoothing.exists_flat_isProjective_smoothing_of_isProper k X.hom hsyn hdim
      hfin
  have : IsProper f := IsProjective.isProper hproj
  have : Flat f := hflat
  have hV : B.Contains (Spec (.of (PowerSeries k))) := BigFppfSite.contains_spec_powerSeries B hk
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hV
  let s := PowerSeriesFamily.specialPoint k
  let y₀ := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hV f) hflat
    (inferInstanceAs (IsProper f)) (inferInstanceAs (LocallyOfFinitePresentation f))
    (fun x => topologicalKrullDimAt_fiber_le_one_of_specialFibre X.hom hdim f e he x)
  -- the special fibre
  have hcart₂ : IsPullback (e.hom ≫ pullback.fst f s) X.hom f s :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he,
      Category.assoc]⟩ e rfl he
  let m₂ : curveFamilyOfScheme X B hZ hk hdim ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hk hV s
      totalMap := schemeSpaceMap (integerSiteMap B hZ
        (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hY
        (e.hom ≫ pullback.fst f s))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap hcart₂ }
  -- the generic fibre
  let η := PowerSeriesFamily.genericPoint k
  have hK := BigFppfSite.residueField_spec_contains B hV η
  have hYη : B.Contains (f.fiber η) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (f.fiberToSpecResidueField η) hK
  have hdimη : topologicalKrullDim (f.fiber η) ≤ 1 :=
    (fiberDimension_le_one_of_specialFibre X.hom hdim f e he η).trans (by simp)
  let x₁ := curveFamilyOfProperFlatMorphism B hZ
    (integerSiteMap B hZ hYη hK (f.fiberToSpecResidueField η))
    (inferInstanceAs (Flat (f.fiberToSpecResidueField η)))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f _) ‹IsProper f›)
    (inferInstanceAs (LocallyOfFinitePresentation (f.fiberToSpecResidueField η))) hdimη
  let m₁ : x₁ ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hK hV ((Spec (.of (PowerSeries k))).fromSpecResidueField η)
      totalMap := schemeSpaceMap (integerSiteMap B hZ hYη hY (f.fiberι η))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap (IsPullback.of_hasPullback f _) }
  have hPx₁ : IsSmoothFamily B hZ x₁ := (Space.isSmooth_yoneda_map_iff B integerBase hZ _).2 hsm
  -- the specialization
  let q₁ := curvesFieldPoint hK x₁ rfl
  let q₂ := curvesFieldPoint hk (curveFamilyOfScheme X B hZ hk hdim) rfl
  have hspec := @pointClass_specializes_of_isHomLift B hZ _ _
    (Functor.congr_obj (curvesSmallEquivalenceOver B hZ).hom.w y₀) q₁ q₂ m₁.baseMap m₂.baseMap
    ((curvesSmallEquivalenceOver B hZ).hom.functor.map m₁)
    ((curvesSmallEquivalenceOver B hZ).hom.functor.map m₂)
    (isHomLift_curvesSmallEquivalenceOver_map m₁) (isHomLift_curvesSmallEquivalenceOver_map m₂) ?_
  · have hmem : Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property q₁ ∈
        curvesPointSet B hZ (IsSmoothFamily B hZ) :=
      ⟨q₁, (isOpenCurvesLocus_isSmoothFamily B hZ).prop_of_hom
        (curvesSmallFamilyCurvesFieldPointIso hK x₁ rfl).hom hPx₁, rfl⟩
    exact closure_mono (Set.singleton_subset_iff.2 hmem) (specializes_iff_mem_closure.1 hspec)
  · have h₁ : Space.schemePoint B integerBase hZ ((curvesFiberedCategory B hZ).val.p.obj y₀)
        (spacePointOfHom q₁ m₁.baseMap) = η :=
      (Spec (.of (PowerSeries k))).fromSpecResidueField_apply η _
    rw [h₁]
    exact (PrimeSpectrum.le_iff_specializes η _).1 bot_le

variable (B hZ) in
/-- **Stacks 0E86.** The inclusion `|Curves^{smooth}| ⊂ |Curves^{lci+}|` is that of an open dense
subset.

`Curves^{smooth}` is the substack of the stack of curves of smooth families of curves, and
`Curves^{lci+}` that of families `X ⟶ S` which are local complete intersection morphisms whose
singular locus is finite over `S` (Stacks 0DZX); `|Curves^{smooth}|` and `|Curves^{lci+}|` are
their images in `|Curves|`, with the topology of Stacks 04Y8, and `|Curves^{lci+}|` carries the
subspace topology. -/
@[stacks 0E86]
theorem curvesPointSet_smooth_isOpen_dense_in_lciPlus :
    curvesPointSet B hZ (IsSmoothFamily B hZ) ⊆ curvesPointSet B hZ (IsLciPlusFamily B hZ) ∧
      IsOpen (Subtype.val ⁻¹' curvesPointSet B hZ (IsSmoothFamily B hZ) :
        Set (curvesPointSet B hZ (IsLciPlusFamily B hZ))) ∧
      Dense (Subtype.val ⁻¹' curvesPointSet B hZ (IsSmoothFamily B hZ) :
        Set (curvesPointSet B hZ (IsLciPlusFamily B hZ))) := by
  have hsub : curvesPointSet B hZ (IsSmoothFamily B hZ) ⊆
      curvesPointSet B hZ (IsLciPlusFamily B hZ) :=
    curvesPointSet_mono (isSmoothFamily_le_lciPlus B hZ)
  refine ⟨hsub, (isOpen_curvesPointSet (isOpenCurvesLocus_isSmoothFamily B hZ)).preimage
    continuous_subtype_val, fun x => ?_⟩
  rw [closure_subtype, Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]
  exact mem_closure_curvesPointSet_isSmoothFamily_of_mem_lciPlus x.2

end AlgebraicGeometry

end
