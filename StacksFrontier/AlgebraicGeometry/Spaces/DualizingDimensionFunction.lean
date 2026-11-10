module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# The dimension function of a dualizing complex on an algebraic space (Stacks 0E53)

Let `X` be a locally Noetherian quasi-separated algebraic space over a scheme `S` and let
`ω_X^•` be a dualizing complex on `X` (Stacks 0E4Z). Stacks 0E53 says that the function
`|X| → ℤ` sending a point `x` to the integer `δ x` for which `ω^•_{X, x̄}[-δ x]` is a normalized
dualizing complex over the étale local ring `𝒪_{X, x̄}` is a dimension function on `|X|`.

## Main definitions

* `IsNormalizingShiftAtGeometricPoints`: Stacks 0E53's condition on `δ`: at every geometric
  point `x̄` of `X`, over `x ∈ |X|`, the stalk `ω^•_{X, x̄}` shifted by `-δ x` is a normalized
  dualizing complex over `𝒪_{X, x̄}`.

## Main results

* `exists_dimensionFunction_of_isDualizingComplex_chart`: a function `δ` normalizing `ω_X^•` at
  every geometric point is a dimension function on `|X|`.
* `exists_dimensionFunction_isNormalizedDualizingComplex_geometricDerivedStalk`: every geometric
  stalk of `ω_X^•` is a dualizing complex, its normalizing shift exists, depends only on the
  point of `|X|` under the geometric point, and is a dimension function.
* `isNormalizedDualizingComplex_geometricDerivedStalk_associatedShiftFunction`: at every
  geometric point over the image of a point `y` of an étale chart, the normalizing shift is the
  value at `y` of the dimension function of Stacks 0AWF on the chart.

## Implementation notes

The integer `δ x` is characterised by a property rather than given by a formula, so in
`exists_dimensionFunction_of_isDualizingComplex_chart` the function `δ` is an argument: any
function with the characterising property is a dimension function.

The dualizing complex is an object `ω` of `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`) with
`AlgebraicGeometry.Space.IsDualizingComplexOnSpace` of Stacks 0E4Z, and its stalk at a geometric
point `x̄` is `AlgebraicGeometry.Space.geometricDerivedStalk`, the derived stalk at the point of
the small étale site attached to `x̄` (Stacks 04K0), over the stalk of the structure sheaf there,
which is `𝒪_{X, x̄}` (Stacks 04KG, `AlgebraicGeometry.Space.pointStalkRingEquiv`).

## References

* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0E4Z](https://stacks.math.columbia.edu/tag/0E4Z)
* [Stacks Project, Tag 0E53](https://stacks.math.columbia.edu/tag/0E53)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

open TopologicalSpace

/-- **Stacks 0E53's condition on `δ`.** Let `K` be an object of `D(𝒪_X)` on a locally Noetherian
algebraic space `X`. The function `δ : |X| → ℤ` *normalizes `K` at the geometric points* if for
every geometric point `x̄` of `X`, lying over `x ∈ |X|`, the shift `K_x̄[-δ x]` of the stalk of `K`
at `x̄` is a normalized dualizing complex over the étale local ring `𝒪_{X, x̄}`.

The stalk is `AlgebraicGeometry.Space.geometricDerivedStalk`, the derived stalk at the point of
the small étale site of Stacks 04K0 attached to `x̄`, over the stalk of the structure sheaf there,
which is `𝒪_{X, x̄}` (Stacks 04KG, `AlgebraicGeometry.Space.pointStalkRingEquiv`); that ring is
Noetherian and local by `AlgebraicGeometry.Space.isNoetherianRing_geometricStalkRing` and
`AlgebraicGeometry.Space.isLocalRing_geometricStalkRing`. -/
def IsNormalizingShiftAtGeometricPoints
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (δ : points B S hS X.1 → ℤ) : Prop :=
  ∀ x : GeometricPoint B S hS X.1,
    letI := isNoetherianRing_geometricStalkRing B S hS X hN x
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((geometricDerivedStalk B S hS x).obj K⟦-δ x.image⟧)

/-- Let `X` be a locally Noetherian quasi-separated algebraic space over a scheme `S` and let
`ω_X^•` be a dualizing complex on `X` (Stacks 0E4Z). Then the function `δ : |X| → ℤ` for which
`ω^•_{X, x̄}[-δ x]` is a normalized dualizing complex over `𝒪_{X, x̄}` at every geometric point
`x̄` of `X` over `x` is a dimension function on `|X|`. -/
@[stacks 0E53]
theorem exists_dimensionFunction_of_isDualizingComplex_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (ω : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (hω : IsDualizingComplexOnSpace B S hS X hX hN ω)
    (δ : points B S hS X → ℤ)
    (hδ : IsNormalizingShiftAtGeometricPoints B S hS ⟨X, hX⟩ hN ω.obj δ) :
    ∃ d : DimensionFunction (points B S hS X), ∀ x : points B S hS X, d x = δ x := by
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  obtain ⟨U, φ, hφSurj, hφEtale⟩ := hX.exists_atlas
  let : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφEtale
  obtain ⟨ωU, hωU, ⟨e⟩⟩ := hω U φ hφEtale
  have hshift : ∀ w : (BigFppfOver.toScheme B S hS).obj U,
      Stacks.Duality.associatedShiftFunction ωU w =
        δ (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm w)) := by
    intro w
    obtain ⟨x, hx, hnorm⟩ := exists_geometricPoint_isNormalizedDualizingComplex B S hS
      ⟨X, hX⟩ hN ω.obj U φ hφEtale ωU hωU e w
    let := isNoetherianRing_geometricStalkRing B S hS ⟨X, hX⟩ hN x
    let := isLocalRing_geometricStalkRing B S hS ⟨X, hX⟩ x
    have h := hδ x
    rw [hx] at h
    exact (hnorm _ h).symm
  obtain ⟨dU, hdU⟩ :=
    (Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hωU).2.2
  have hsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U φ).mp hφSurj
  refine exists_dimensionFunction_of_generalizingMap
    ((continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS U).symm.continuous)
    (hsurjPts.comp (schemePointsHomeomorph B S hS U).symm.surjective)
    (((schemePointsHomeomorph B S hS U).symm.isOpenEmbedding.generalizingMap).comp
      (generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hXdec U φ hφEtale)) δ dU ?_
  intro w
  change dU w = δ (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm w))
  rw [hdU w]
  exact hshift w

/-! ### The normalizing shift at every geometric point -/

/-- A complex whose extension of scalars along a bijective homomorphism of Noetherian local rings
is a normalized dualizing complex is itself one. -/
theorem _root_.Dualizing.isNormalizedDualizingComplex_of_extendScalars_of_bijective
    {A A' : Type u} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']
    [IsNoetherianRing A] [IsNoetherianRing A'] (g : A →+* A') (hg : Function.Bijective g)
    (K : DerivedCategory (ModuleCat.{u} A))
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g)]
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.extendScalars.{u, u, u} g).mapDerivedCategory.obj K)) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} K := by
  let e := RingEquiv.ofBijective g hg
  let g' : A' →+* A := e.symm.toRingHom
  have hg' : Function.Bijective g' := e.symm.bijective
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g') :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (RingHom.Flat.of_bijective hg')
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mp
    (Dualizing.isNormalizedDualizingComplex_extendScalars_of_bijective g' hg' _ hK)
  have hid : g'.comp g = RingHom.id A := by
    ext a
    exact e.symm_apply_apply a
  let c : ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.extendScalars.{u, u, u} g' ≅
      𝟭 (ModuleCat.{u} A) :=
    (ModuleCat.extendScalarsComp g g').symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars hid) ≪≫ ModuleCat.extendScalarsId A
  exact (Stacks.DerivedGlueing.mapDerivedCategoryCompIso _ _).app K ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr c).app K ≪≫
    StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso.app K

/-- **Normalized geometric stalks descend along an étale chart.** If the stalk of `K|_V` at a
geometric point `p` of `h_V` is, shifted by `-m`, a normalized dualizing complex, then so is the
stalk of `K` at the image `ψ(p)`. This is the converse of
`AlgebraicGeometry.Space.isNormalizedDualizingComplex_geometricDerivedStalk_restriction`. -/
theorem isNormalizedDualizingComplex_geometricDerivedStalk_of_restriction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X.1) (hψ : IsEtale B S hS ψ)
    (p : GeometricPoint B S hS (yoneda.obj V)) (m : ℤ)
    (hm : letI := isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
      letI := isLocalRing_geometricStalkRing B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
      Dualizing.IsNormalizedDualizingComplex.{u, u}
        ((geometricDerivedStalk B S hS
            (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p).obj
          ((representedChartDerivedRestriction B S hS X.2 V ψ hψ).obj K)⟦-m⟧)) :
    letI := isNoetherianRing_geometricStalkRing B S hS X hN (geometricPointMap ψ p)
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((geometricDerivedStalk B S hS (geometricPointMap ψ p)).obj K⟦-m⟧) := by
  let f : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk ψ
  obtain ⟨eC1⟩ := nonempty_geometricDerivedStalk_etaleModulePullback_iso B S hS f hψ p K
  have hg := bijective_smallEtaleStalkPullbackRingMap B S hS f hψ p
  let : IsNoetherianRing (Stacks.ringFiber
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom p) X.2)
      (smallEtaleRingedTopos B S hS X).O.obj) :=
    isNoetherianRing_geometricStalkRing B S hS X hN (geometricPointMap ψ p)
  let : IsLocalRing (Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap f.hom p) X.2)
      (smallEtaleRingedTopos B S hS X).O.obj) :=
    isLocalRing_geometricStalkRing B S hS X (geometricPointMap ψ p)
  let : IsNoetherianRing (Stacks.ringFiber (etaleSitePoint B S hS (yoneda.obj V) p
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
      (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) :=
    isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
  let : IsLocalRing (Stacks.ringFiber (etaleSitePoint B S hS (yoneda.obj V) p
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
      (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) :=
    isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (smallEtaleStalkPullbackRingMap B S hS f p)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (RingHom.Flat.of_bijective hg)
  let : IsNoetherianRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) :=
    isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
  let : IsLocalRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) :=
    isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  refine Dualizing.isNormalizedDualizingComplex_of_extendScalars_of_bijective _ hg _ ?_
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mpr hm
  exact ((ModuleCat.extendScalars.{u, u, u}
      (smallEtaleStalkPullbackRingMap B S hS f p)).mapDerivedCategory.commShiftIso (-m)).app _ ≪≫
    (shiftFunctor _ (-m)).mapIso eC1.symm

/-- **The normalizing shift at an arbitrary geometric point.** Let `K` be an object of `D(𝒪_X)`
whose restriction to an étale chart `φ : h_U ⟶ X` is `ε^*ω_U` for a dualizing complex `ω_U` on
the scheme `U`. Then at *every* geometric point `x̄` of `X` lying over the image of a point `y`
of `U`, the stalk `K_x̄` shifted by minus the value at `y` of the dimension function of Stacks 0AWF
for `ω_U` is a normalized dualizing complex over `𝒪_{X, x̄}`. -/
theorem isNormalizedDualizingComplex_geometricDerivedStalk_associatedShiftFunction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X.1)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (ωU : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hωU : Stacks.Duality.IsDualizingComplex ωU)
    (e : (representedChartDerivedRestriction B S hS X.2 U φ
        (isEtale_of_presheaf_etale B S hS hφ)).obj K ≅
      (representedDerivedAssociatedModule B S hS U).obj ωU)
    (y : (BigFppfOver.toScheme B S hS).obj U) (x : GeometricPoint B S hS X.1)
    (hx : x.image = pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm y)) :
    letI := isNoetherianRing_geometricStalkRing B S hS X hN x
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((geometricDerivedStalk B S hS x).obj K⟦-Stacks.Duality.associatedShiftFunction ωU y⟧) := by
  obtain ⟨-, ⟨W, hW₀, rfl⟩, hyW, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW₀
  let : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj U, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hωU W hW
  have hshift : Stacks.Duality.associatedShiftFunction ωU y =
      Dualizing.dualizingDimension.{u, u} M (hW.primeIdealOf ⟨y, hyW⟩) :=
    Stacks.Duality.associatedShiftFunction_eq_dualizingDimension hW M ⟨hM, ⟨eM⟩⟩ y hyW
  let Ac : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk φ, hφ⟩
  let W' : BigFppfOver B S hS := chartOpenOver B S hS Ac W
  let q : W' ⟶ U := chartOpenOverι B S hS Ac W
  have hTq : (BigFppfOver.toScheme B S hS).map q = Scheme.Opens.ι W := rfl
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q) :=
    hTq ▸ Scheme.Opens.instIsOpenImmersionι (U := W)
  have hqEt : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  have hqφ : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
    isEtale_schemeSpaceMap B S hS _ q hqEt
  have hψ := etale_comp_of_scheme B S hS q φ hqEt hφ
  have hφE := isEtale_of_presheaf_etale B S hS hφ
  have hψE := isEtale_of_presheaf_etale B S hS hψ
  let y' : (BigFppfOver.toScheme B S hS).obj W' := ⟨y, hyW⟩
  have hu : pointsMap B S hS (yoneda.obj W') (yoneda.map q ≫ φ)
      ((pointsEquivScheme B S hS W').symm y') = x.image := by
    rw [hx, pointsMap_comp]
    refine congrArg (pointsMap B S hS (yoneda.obj U) φ) ?_
    apply (pointsEquivScheme B S hS U).injective
    rw [Equiv.apply_symm_apply]
    change pointsToScheme B S hS U (pointsMap B S hS _ (yoneda.map q) _) = y
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map q ((pointsEquivScheme B S hS W')
      ((pointsEquivScheme B S hS W').symm y')) = y
    rw [Equiv.apply_symm_apply]
    rfl
  obtain ⟨p, hp, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W') X.2 (yoneda.map q ≫ φ) hψE x _ hu
  have hxp : geometricPointMap (yoneda.map q ≫ φ) p = x := Subtype.ext hval
  subst hxp
  let eW : (representedChartDerivedRestriction B S hS X.2 W' (yoneda.map q ≫ φ) hψE).obj K ≅
      (representedDerivedAssociatedModule B S hS W').obj
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, W) ⋙
          Scheme.Modules.restrictFunctor hW.isoSpec.hom).mapDerivedCategory.obj M) :=
    (representedChartDerivedRestrictionCompIso B S hS X.2 φ hφE q hqφ hψE).app K ≪≫
      (representedDerivedPullback B S hS q hqφ).mapIso e ≪≫
      (representedDerivedAssociatedModulePullbackIso B S hS q hqφ).app ωU ≪≫
      (representedDerivedAssociatedModule B S hS W').mapIso
        ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory
            ((BigFppfOver.toScheme B S hS).map q)).app ωU ≪≫
          (Stacks.DerivedGlueing.mapDerivedCategoryCongr
            (Scheme.Modules.restrictFunctorIsoPullback
              ((BigFppfOver.toScheme B S hS).map q)).symm).app ωU ≪≫ eM)
  obtain ⟨γ, hγ, ⟨eF⟩⟩ := exists_representedAffineStalkRingHom_iso B S hS W'
    Γ((BigFppfOver.toScheme B S hS).obj U, W) hW.isoSpec p
  let N := selfNeighborhood B S hS W' p
  have hz : chartPoint B S hS (yoneda.obj W') N = y' := by
    change pointsToScheme B S hS W' p.image = y'
    rw [hp]
    exact (pointsEquivScheme B S hS W').apply_symm_apply y'
  let α : Γ((BigFppfOver.toScheme B S hS).obj U, W) →+*
      chartLocalRing B S hS (yoneda.obj W') N :=
    ((W : Scheme.{u}).presheaf.germ ⊤ (chartPoint B S hS (yoneda.obj W') N) trivial).hom.comp
      (Scheme.Opens.topIso W).inv.hom
  have hα := isLocalization_stalk_toScheme hW (chartPoint B S hS (yoneda.obj W') N)
  have hγα : ∀ a, pointStalkRingEquiv B S hS
      ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ p (γ a) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W')
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W') N (α a) := by
    intro a
    rw [hγ a, IsAffineOpen.isoSpec_hom_appTop]
    refine (congrArg (etaleLocalRingGerm B S hS (yoneda.obj W') p (Opposite.op N))
      (congrArg (fun t => (Scheme.Opens.topIso W).inv.hom t)
        (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, W))
          a))).trans ?_
    exact (chartLocalRingToEtaleLocalRing_germ B S hS (yoneda.obj W')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W') N
        ((Scheme.Opens.topIso W).inv.hom a)).symm
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W') :=
    inferInstanceAs (IsLocallyNoetherian (W : Scheme.{u}))
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} γ) :=
    preservesFiniteLimits_extendScalars_of_iso B S hS W' _ hW.isoSpec p γ eF
  have hn := isNormalizedDualizingComplex_extendScalars_geometricStalkRing B S hS W' p
    Γ((BigFppfOver.toScheme B S hS).obj U, W)
    (hW.primeIdealOf (chartPoint B S hS (yoneda.obj W') N)) α hα γ hγα M hM
  obtain ⟨e₃⟩ := nonempty_geometricDerivedStalk_representedTilde_iso B S hS W' _ hW.isoSpec p
    γ eF M
  let := isNoetherianRing_geometricStalkRing_yoneda B S hS W' p
  let := isLocalRing_geometricStalkRing B S hS
    ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ p
  have hdim : Dualizing.dualizingDimension.{u, u} M
      (hW.primeIdealOf (chartPoint B S hS (yoneda.obj W') N)) =
      Stacks.Duality.associatedShiftFunction ωU y := by
    rw [hshift]
    exact congrArg (fun z => Dualizing.dualizingDimension.{u, u} M (hW.primeIdealOf z)) hz
  rw [hdim] at hn
  refine isNormalizedDualizingComplex_geometricDerivedStalk_of_restriction B S hS X hN K W'
    (yoneda.map q ≫ φ) hψE p _ ?_
  exact (Dualizing.isNormalizedDualizingComplex_congr.{u, u}
    ((shiftFunctor _ (-Stacks.Duality.associatedShiftFunction ωU y)).mapIso
      ((geometricDerivedStalk B S hS
        (X := ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩) p).mapIso eW ≪≫
          e₃))).mpr hn

/-- Let `X` be a locally Noetherian quasi-separated algebraic space over a scheme `S` and let
`ω_X^•` be a dualizing complex on `X` (Stacks 0E4Z). Then there is a dimension function `δ` on
`|X|` such that at every geometric point `x̄` of `X`, lying over `x ∈ |X|`, the stalk `ω_{X, x̄}^•`
is a dualizing complex over the étale local ring `𝒪_{X, x̄}` and `δ x` is the unique integer `n`
for which `ω_{X, x̄}^•[-n]` is a normalized dualizing complex. In particular the normalizing shift
exists at every geometric point and depends only on the point of `|X|` under it. -/
@[stacks 0E53]
theorem exists_dimensionFunction_isNormalizedDualizingComplex_geometricDerivedStalk
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (ω : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (hω : IsDualizingComplexOnSpace B S hS X hX hN ω) :
    ∃ δ : DimensionFunction (points B S hS X),
      ∀ x : GeometricPoint B S hS X,
        letI := isNoetherianRing_geometricStalkRing B S hS ⟨X, hX⟩ hN x
        letI := isLocalRing_geometricStalkRing B S hS ⟨X, hX⟩ x
        Dualizing.IsDualizingComplex ((geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj) ∧
          ∀ n : ℤ, Dualizing.IsNormalizedDualizingComplex.{u, u}
              ((geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj⟦-n⟧) ↔ n = δ x.image := by
  obtain ⟨U, φ, hφSurj, hφEtale⟩ := hX.exists_atlas
  let : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφEtale
  obtain ⟨ωU, hωU, ⟨e⟩⟩ := hω U φ hφEtale
  have hsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U φ).mp hφSurj
  choose w hw using hsurjPts
  let δ₀ : points B S hS X → ℤ := fun x =>
    Stacks.Duality.associatedShiftFunction ωU (pointsEquivScheme B S hS U (w x))
  have hnorm : ∀ x : GeometricPoint B S hS X,
      let := isNoetherianRing_geometricStalkRing B S hS ⟨X, hX⟩ hN x
      let := isLocalRing_geometricStalkRing B S hS ⟨X, hX⟩ x
      Dualizing.IsNormalizedDualizingComplex.{u, u}
        ((geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj⟦-δ₀ x.image⟧) := by
    intro x
    refine isNormalizedDualizingComplex_geometricDerivedStalk_associatedShiftFunction B S hS
      ⟨X, hX⟩ hN ω.obj U φ hφEtale ωU hωU e _ x ?_
    rw [Equiv.symm_apply_apply, hw]
  obtain ⟨d, hd⟩ := exists_dimensionFunction_of_isDualizingComplex_chart B S hS X hX hXqs hN ω hω
    δ₀ hnorm
  refine ⟨d, fun x => ?_⟩
  let := isNoetherianRing_geometricStalkRing B S hS ⟨X, hX⟩ hN x
  let := isLocalRing_geometricStalkRing B S hS ⟨X, hX⟩ x
  have hx : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj⟦-d x.image⟧) := by
    rw [hd]
    exact hnorm x
  refine ⟨?_, Dualizing.isNormalizedDualizingComplex_shift_iff_eq.{u, u} _ _ hx⟩
  have hK := Dualizing.isDualizingComplex_shift _ hx.1 (d x.image)
  let eK : ((geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj⟦-d x.image⟧)⟦d x.image⟧ ≅
      (geometricDerivedStalk B S hS (X := ⟨X, hX⟩) x).obj ω.obj :=
    (shiftFunctorCompIsoId _ (-d x.image) (d x.image) (by omega)).app _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hge, hle, hinj, ⟨eK.symm ≪≫ eI⟩⟩
  · intro i
    let := hK.finiteCohomology i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor _ i).mapIso eK).toLinearEquiv
  · intro I hI hinj hbound
    obtain ⟨eI⟩ := hI
    exact hK.homothetyQuasiIso I ⟨eI ≪≫ eK.symm⟩ hinj hbound

end AlgebraicGeometry.Space

end
