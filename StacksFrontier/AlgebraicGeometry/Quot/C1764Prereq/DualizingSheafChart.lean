module

public import StacksFrontier.AlgebraicGeometry.Spaces.C1764Prereq.RepresentedRightAdjointHomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingSheafCurveFibres
public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafNodal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationEtaleSource
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof

/-!
# The relative dualizing complex of a prestable family on a scheme chart

Let `f : X ⟶ S` be a prestable family of curves and `(ω^•_{X/S}, τ)` a relative dualizing
complex (Stacks 0E5X). By Stacks 0E6F the family is a scheme étale locally on `S`: there are
cartesian squares `p : Z ⟶ X` over étale `φ : U ⟶ S` with `Z ⟶ U` a morphism of schemes, and `U`
may be taken affine. This file computes `Lp^*ω^•_{X/S}` on such an affine chart. The defining
property of a relative dualizing complex identifies it with the right adjoint `a(𝒪_U)` of
`Rf_*` for the chart, which corresponds to the twisted inverse image `a_0(𝒪_U)` of the morphism
of schemes `Z ⟶ U` (Stacks 0E6E); the latter is a proper, flat, surjective at-worst-nodal
morphism of relative dimension one, for which `a_0(𝒪_U)` has cohomology only in degree `-1`
and an invertible cohomology sheaf there (Stacks 0E6P, 0E6R for schemes).

## Main results

* `AlgebraicGeometry.C1764Prereq.isZero_homology_relativeDualizingComplex_of_isAtWorstNodal`
  and `AlgebraicGeometry.C1764Prereq.isInvertible_relativeDualizingSheaf_of_isAtWorstNodal`:
  Stacks 0E6P and 0E6R for an at-worst-nodal family of schemes over an affine base.
* `AlgebraicGeometry.C1764Prereq.homologyChartIso`: the cohomology sheaves of `Lp^*ω^•_{X/S}`
  on an affine chart, read on the scheme.
* `AlgebraicGeometry.C1764Prereq.isZero_homology_chart` and
  `AlgebraicGeometry.C1764Prereq.isInvertibleModule_homology_chart`: Stacks 0E6P and 0E6R on an
  affine chart of a prestable family.
* `AlgebraicGeometry.C1764Prereq.exists_affine_chart`: affine étale scheme charts cover the total
  space.

## References

* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.C1764Prereq

section Scheme

variable {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f]

/-- A surjective at-worst-nodal morphism of relative dimension one has Gorenstein fibres,
equidimensional of dimension one, each presented by the scheme-theoretic fibre. -/
theorem curveFibres_hasGorensteinCurveFibres_of_isAtWorstNodal
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (hsurj : ∀ s : S, ∃ x : X, f x = s) :
    Stacks.Duality.CurveFibres.HasGorensteinCurveFibres f := by
  intro s
  obtain ⟨x, rfl⟩ := hsurj s
  obtain ⟨h₁, h₂, h₃⟩ := C1590Private.hasGorensteinCurveFibres_of_isAtWorstNodal hf x
  exact ⟨_, _, _, IsPullback.of_hasPullback f (S.fromSpecResidueField (f x)), h₁, h₂, h₃⟩

/-- **Stacks 0E6P for a surjective at-worst-nodal family of schemes over an affine base**: the
relative dualizing complex `a(𝒪_S)` has no cohomology outside degree `-1`. -/
theorem isZero_homology_relativeDualizingComplex_of_isAtWorstNodal
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (hsurj : ∀ s : S, ∃ x : X, f x = s) (i : ℤ)
    (hi : i ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (C1590Private.relativeDualizingComplex f).obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact (Stacks.Duality.CurveFibres.isZero_homology_relativeDualizingComplex f
    (curveFibres_hasGorensteinCurveFibres_of_isAtWorstNodal f hf hsurj) i hi).of_iso
    (((StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso
      (HasDerivedCategory.standard X.Modules) (Scheme.Modules.hasDerivedCategory X) i).app
        _).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules i).mapIso
        ((ObjectProperty.ι _).mapIso
          (Stacks.Duality.StandardModel.relativeDualizingComplexModelIso f))).symm

/-- **Stacks 0E6R for an at-worst-nodal family of schemes over an affine base**: the relative
dualizing sheaf `H^{-1}(a(𝒪_S))` is invertible. -/
theorem isInvertible_relativeDualizingSheaf_of_isAtWorstNodal
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (C1590Private.relativeDualizingSheaf f) :=
  C1590Private.isInvertible_relativeDualizingSheaf f
    (C1590Private.hasGorensteinCurveFibres_of_isAtWorstNodal hf)

end Scheme

section Chart

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective SheafOfModules.instAbelian

variable {X : CurveFamily B hZ} {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base} {q : Z ⟶ U}
  {p : schemeSpace Z ⟶ X.total}

/-- On a scheme chart `Z ⟶ U` of a prestable family, the morphism of schemes `Z ⟶ U` is
at-worst-nodal of relative dimension one (a base change of the family). -/
theorem isAtWorstNodal_toScheme_map_of_chart (hX : IsPrestableCurveFamily B hZ X)
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    IsAtWorstNodalOfRelativeDimensionOne ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget q).1
    ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
      hZ).of_isPullback hsq hX.1)

/-- The base change of a scheme chart along `ρ : V ⟶ U` is cartesian over `ρ ≫ φ`. -/
private theorem isPullback_pullback_fst_comp_of_chart {V : BigFppfOver B integerBase hZ}
    (ρ : V ⟶ U) (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    IsPullback (schemeSpaceMap (pullback.fst q ρ) ≫ p) (schemeSpaceMap (pullback.snd q ρ))
      X.toBase (schemeSpaceMap (ρ ≫ φ)) := by
  rw [schemeSpaceMap_comp]
  exact (isPullback_schemeSpaceMap (IsPullback.of_hasPullback q ρ)).paste_horiz hsq

/-- On a scheme chart `Z ⟶ U` of a prestable family, the morphism of schemes `Z ⟶ U` is
surjective: its fibre over a point `u` presents the fibre of the family over the image of `u`,
which is a curve, hence nonempty. -/
theorem exists_toScheme_map_eq_of_chart (hX : IsPrestableCurveFamily B hZ X)
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    ∃ z : (BigFppfOver.toScheme B integerBase hZ).obj Z,
      (BigFppfOver.toScheme B integerBase hZ).map q z = u := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj :=
    Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom
      (C1590Private.residueFieldValuedPoint U u)
  let ρ : (C1590Private.residueFieldValuedPoint U u).siteObject ⟶ U :=
    (C1590Private.residueFieldValuedPoint U u).value
  have hpres : IsPullback ((schemeSpaceMap (pullback.fst q ρ) ≫ p).hom)
      (yoneda.map (pullback.snd q ρ)) X.toBase.hom (yonedaEquiv.symm Q.value) := by
    exact AlgebraicSpaces.isPullback_hom B integerBase hZ
      (isPullback_pullback_fst_comp_of_chart ρ hsq)
  obtain ⟨-, hdim, -, -⟩ := C1590Private.fibre_properties_of_isPrestableCurveFamily hX Q _ _ hpres
  have hne : Nonempty (T.obj (pullback q ρ)) := by
    by_contra h
    have : IsEmpty (T.obj (pullback q ρ)) := not_nonempty_iff.1 h
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 inferInstance] at hdim
    exact absurd hdim (by decide)
  obtain ⟨y⟩ := hne
  refine ⟨T.map (pullback.fst q ρ) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← T.map_comp, pullback.condition, T.map_comp,
    Scheme.Hom.comp_apply]
  show (T.obj U).fromSpecResidueField u _ = u
  exact (T.obj U).fromSpecResidueField_apply u _

/-- The morphism of schemes underlying a scheme chart of a family of curves is proper. -/
theorem isProper_toScheme_map_of_chart
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hsq

/-- The morphism of schemes underlying a scheme chart of a family of curves is proper, flat and
locally of finite presentation. -/
private theorem isProper_flat_lfp_toScheme_map_of_chart
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) ∧
      Flat ((BigFppfOver.toScheme B integerBase hZ).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  ⟨isProper_toScheme_map_of_chart hsq, X.flat_toScheme_map_of_isPullback hsq,
    X.locallyOfFinitePresentation_toScheme_map_of_isPullback hsq⟩

/-- **The cohomology sheaves of a relative dualizing complex on an affine scheme chart.** Let
`Z ⟶ U` be a scheme chart of a family of curves over an affine `U`, cartesian over
`φ : U ⟶ S`, with `p : Z ⟶ X`. The `i`-th cohomology sheaf of `Lp^*ω^•_{X/S}` is the pullback
along `ε : Z ⟶ Z_0` of the `i`-th cohomology sheaf of `a_0(𝒪_U)` for the morphism of schemes
`Z_0 ⟶ U_0`: the defining property of a relative dualizing complex identifies `Lp^*ω^•_{X/S}`
with the right adjoint `a(𝒪_U)` of the space morphism (Stacks 0E5X), which corresponds to `a_0`
(Stacks 0E6E). -/
def homologyChartIso
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)] (i : ℤ) :
    haveI := isProper_toScheme_map_of_chart hsq
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((Space.smallEtaleDerivedModulePullback B integerBase hZ p).obj D.ω) ≅
      (Space.representedZariskiModulePullbackRepresentedZariskiPullbackExact B integerBase hZ
        Z).obj ((DerivedCategory.homologyFunctor
          ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules i).obj
          (C1590Private.relativeDualizingComplex
            ((BigFppfOver.toScheme B integerBase hZ).map q)).obj) := by
  have hY' : Space.IsAffineSpace B integerBase hZ (schemeSpace U).1 :=
    Space.isAffineSpace_yoneda B integerBase hZ U inferInstance
  let eω := (D.isAffineBaseChangePair (schemeSpaceMap q) (schemeSpaceMap φ) p hsq hY').choose
  have hXqc := Space.isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B integerBase hZ
    (schemeSpaceMap q).hom hY'
    (Space.isQuasiCompact_of_isPullback_of_isFinitePresentation hsq X.finitePresentation)
  have hXqs := Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B integerBase
    hZ B.contains_terminal (schemeSpaceMap q).hom (ObjectProperty.FullSubcategory.property _) hY'
    (Space.isQuasiSeparated_of_isPullback_of_isFinitePresentation hsq X.finitePresentation)
  have hYqs := Space.isAbsolutelyQuasiSeparated_of_isAffineSpace B integerBase hZ
    B.contains_terminal hY'
  have hYqc := Space.isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ U inferInstance
  exact (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso eω ≪≫
    homologyRightAdjointStructureSheafIso B.contains_terminal q hXqc hXqs hYqc hYqs i

/-- **Stacks 0E6P on an affine scheme chart of a prestable family**: the derived pullback of a
relative dualizing complex to an affine scheme chart has no cohomology outside degree `-1`. -/
theorem isZero_homology_chart (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)] (i : ℤ) (hi : i ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((Space.smallEtaleDerivedModulePullback B integerBase hZ p).obj D.ω)) := by
  obtain ⟨_, _, _⟩ := isProper_flat_lfp_toScheme_map_of_chart hsq
  exact (Functor.map_isZero
    (Space.representedZariskiModulePullbackRepresentedZariskiPullbackExact B integerBase hZ Z)
    (isZero_homology_relativeDualizingComplex_of_isAtWorstNodal _
      (isAtWorstNodal_toScheme_map_of_chart hX hsq) (exists_toScheme_map_eq_of_chart hX hsq)
      i hi)).of_iso (homologyChartIso D hsq i)

/-- **Stacks 0E6R on an affine scheme chart of a prestable family**: the degree `-1` cohomology
sheaf of the derived pullback of a relative dualizing complex to an affine scheme chart is
invertible. It is the module associated with the relative dualizing sheaf of the chart, which is
invertible. -/
theorem isInvertibleModule_homology_chart (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)] :
    Space.IsInvertibleModule (schemeSpace Z)
      ((@DerivedCategory.homologyFunctor
        (SheafOfModules (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace Z))) _ _
        (HasDerivedCategory.standard _) (-1)).obj
        ((Space.smallEtaleDerivedModulePullback B integerBase hZ p).obj D.ω)) := by
  obtain ⟨_, _, _⟩ := isProper_flat_lfp_toScheme_map_of_chart hsq
  have h₂ : Space.IsInvertibleModule (schemeSpace Z)
      ((Space.representedAssociatedModule B integerBase hZ Z
        (isAlgebraicSpace_yoneda B integerBase hZ Z)).obj
        ((DerivedCategory.homologyFunctor ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules
          (-1)).obj (C1590Private.relativeDualizingComplex
            ((BigFppfOver.toScheme B integerBase hZ).map q)).obj)) :=
    Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B integerBase hZ Z _ (isInvertible_relativeDualizingSheaf_of_isAtWorstNodal _
        (isAtWorstNodal_toScheme_map_of_chart hX hsq))
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _
    ((homologyChartIso D hsq (-1)) ≪≫
      (Space.representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B integerBase hZ Z).app _).symm

/-- **Affine étale scheme charts cover a family of curves** (Stacks 0E6F). Every point `x` of the
total space of a family of curves lies in the image of the étale morphism `p : Z ⟶ X` of a
scheme chart: a cartesian square over an étale `φ : U ⟶ S` from an affine scheme `U`. -/
theorem exists_affine_chart (X : CurveFamily B hZ)
    (x : Space.points B integerBase hZ X.total.1) :
    ∃ (U Z : BigFppfOver B integerBase hZ) (φ : U ⟶ X.base) (q : Z ⟶ U)
      (p : schemeSpace Z ⟶ X.total),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
        Space.IsEtale B integerBase hZ p.hom ∧
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ) ∧
        x ∈ Set.range (Space.pointsMap B integerBase hZ (schemeSpace Z).1 p.hom) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let s₀ : T.obj X.base := Space.pointsEquivScheme B integerBase hZ X.base
    (Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x)
  obtain ⟨U, Z, φ, q, p, hφ, ⟨u, hu⟩, hsq⟩ := C1590Private.hasEtaleLocalSchemeCharts B hZ X s₀
  obtain ⟨A, hA, huA, -⟩ := exists_isAffineOpen_mem_and_subset (X := T.obj U) (x := u)
    (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  have hAc : B.Contains A.toScheme := B.contains_of_mono A.ι U.left.2
  let ι : BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι ⟶ U :=
    BigFppfOver.siteMapOver B integerBase hZ U hAc A.ι
  have hsqA := isPullback_pullback_fst_comp_of_chart ι hsq
  have : IsAffine (T.obj (BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι)) :=
    inferInstanceAs (IsAffine A.toScheme)
  have het : Etale (T.map (ι ≫ φ)) := by
    have : Etale (T.map φ) := hφ
    have : Etale (T.map ι) := inferInstanceAs (Etale A.ι)
    rw [T.map_comp]
    infer_instance
  have hpet : Space.IsEtale B integerBase hZ (schemeSpaceMap (pullback.fst q ι) ≫ p).hom :=
    Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ hsqA.flip
      ((Space.isEtale_yoneda_map_iff B integerBase hZ (ι ≫ φ)).2 het)
  obtain ⟨a, ha⟩ : u ∈ Set.range (T.map ι) := by
    rw [show Set.range (T.map ι) = A from A.range_ι]
    exact huA
  have hab : Space.pointsMap B integerBase hZ X.total.1 X.toBase.hom x =
      Space.pointsMap B integerBase hZ _ (yoneda.map (ι ≫ φ))
        ((Space.pointsEquivScheme B integerBase hZ _).symm a) := by
    rw [Space.ChartBranch.pointsEquivScheme_symm_pointsMap]
    apply (Space.pointsEquivScheme B integerBase hZ X.base).injective
    rw [Equiv.apply_symm_apply, T.map_comp, Scheme.Hom.comp_apply, ha, hu]
    rfl
  obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hsqA) x
    ((Space.pointsEquivScheme B integerBase hZ _).symm a) hab
  exact ⟨_, _, _, _, _, inferInstance, hpet, hsqA, w, hw⟩

end Chart

end AlgebraicGeometry.C1764Prereq

end
