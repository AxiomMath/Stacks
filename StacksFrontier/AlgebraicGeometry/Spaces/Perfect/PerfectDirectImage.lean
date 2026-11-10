module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImageChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EtaleDerivedPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfect direct images of algebraic spaces (Stacks 08IS)

Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism which is locally of finite
type and quasi-separated.  If `E ∈ D^b_{Coh}(𝒪_X)` has cohomology sheaves with support proper
over `Y` and has finite tor dimension as an object of `D(f⁻¹𝒪_Y)`, then `Rf_*E` is perfect.

## Main results

* `AlgebraicGeometry.Space.exists_isQuasiCompactSpace_openSubspace_of_isCompact`: a compact set
  of points lies in a quasi-compact open subspace.
* `AlgebraicGeometry.Space.isCompact_of_isProperOver`: a closed set proper over a quasi-compact
  base is compact.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_openSubspaceOfPoints`: an open
  subspace containing a closed set, with the complement of that set, is an elementary
  distinguished square.
* `AlgebraicGeometry.Space.nonempty_derivedModulePushforward_iso_of_cohomologySupportedOn`: for
  `E` supported on the complement of `U` in an elementary distinguished square `(U, j : V ⟶ X)`,
  `Rf_*E ≅ R(j ≫ f)_*(E|_V)`.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_hasProperSupport`: `Rf_*E` is
  perfect.

## References

* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 0CZH](https://stacks.math.columbia.edu/tag/0CZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

open DerivedCategoryB

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A compact set of points of an algebraic space lies in a quasi-compact open subspace.** -/
theorem exists_isQuasiCompactSpace_openSubspace_of_isCompact
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (A : Set (points B S hS X)) (hA : IsCompact A) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ IsQuasiCompactSpace B S hS U.toFunctor ∧
      A ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  let N : points B S hS X → Set (points B S hS X) := fun x => Classical.choose
    ((hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp
      (Filter.univ_mem : (Set.univ : Set (points B S hS X)) ∈ nhds x))
  have hN : ∀ x, IsOpen (N x) ∧ IsCompact (N x) ∧ x ∈ N x := fun x =>
    (Classical.choose_spec ((hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp
      (Filter.univ_mem : (Set.univ : Set (points B S hS X)) ∈ nhds x))).1
  obtain ⟨t, -, ht⟩ := hA.elim_nhds_subcover N fun x _ => (hN x).1.mem_nhds (hN x).2.2
  let W : Set (points B S hS X) := ⋃ x ∈ t, N x
  have hWopen : IsOpen W := isOpen_biUnion fun x _ => (hN x).1
  have hWcompact : IsCompact W := t.finite_toSet.isCompact_biUnion fun x _ => (hN x).2.1
  have hU := isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X) W
  refine ⟨openSubspaceOfPoints B S hS X W, hU,
    isQuasiCompactSpace_of_isCompact_range B S hS hX hU (by rw [hrange]; exact hWcompact),
    by rw [hrange]; exact ht⟩

/-- **A closed set of points proper over a quasi-compact algebraic space is compact.** -/
theorem isCompact_of_isProperOver {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) (hTp : IsProperOver B S hS hX hY f hf T hT) :
    IsCompact T := by
  let Z := reducedClosedSubspace B S hS X hX T hT
  have hZ : IsAlgebraicSpace B S hS Z.toFunctor :=
    (isClosedSubspace_reducedClosedSubspace' B S hS hX T hT).1
  have hZqc : IsQuasiCompactSpace B S hS Z.toFunctor :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc _ hTp.2.1.2
  have : CompactSpace (points B S hS Z.toFunctor) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS Z.toFunctor hZ).1 hZqc
  rw [← range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT]
  exact isCompact_range (continuous_pointsMap B S hS Z.ι)

/-- **An open subspace containing a closed set of points, with the open complement of that set,
is an elementary distinguished square** (Stacks 08GM). -/
theorem isElementaryDistinguishedSquare_openSubspaceOfPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (V : Subfunctor X)
    (hV : IsOpenSubspace B S hS V) (hTV : T ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    IsElementaryDistinguishedSquare B S hS hX (openSubspaceOfPoints B S hS X Tᶜ) V.ι := by
  have hrange : (Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS X Tᶜ).toFunctor
      (openSubspaceOfPoints B S hS X Tᶜ).ι))ᶜ = T := by
    rw [range_pointsMap_ι_openSubspaceOfPoints, compl_compl]
  have hcl : IsClosed (Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS X Tᶜ).toFunctor
      (openSubspaceOfPoints B S hS X Tᶜ).ι))ᶜ := by rw [hrange]; exact hT
  refine ⟨hV.1, isOpenSubspace_openSubspaceOfPoints B S hS hX _ hT.isOpen_compl,
    isEtale_ι_of_isOpenSubspace hV, hcl, ?_⟩
  let D := reducedClosedSubspace B S hS X hX _ hcl
  have hDrange : Set.range (pointsMap B S hS D.toFunctor D.ι) = T :=
    (range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ hcl).trans hrange
  have hbij : ∀ A : BigFppfOver B S hS,
      Function.Bijective ((D.fromPreimage V.ι).app (Opposite.op A)) := by
    intro A
    constructor
    · exact fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z => z.val) hxy))
    · intro y
      have hfac : Set.range (pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm y.val)) ⊆
          Set.range (pointsMap B S hS V.toFunctor V.ι) := by
        have hy : yonedaEquiv.symm y.val = yonedaEquiv.symm y ≫ D.ι := by
          apply yonedaEquiv.injective
          simp [yonedaEquiv_comp]
        rw [hy, pointsMap_comp]
        exact (Set.range_comp_subset_range _ _).trans (hDrange ▸ hTV)
      obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hX
        (isAlgebraicSpace_yoneda B S hS A) V hV (yonedaEquiv.symm y.val)).2 hfac
      have hgv : (yonedaEquiv g).val = y.val := by
        have := congrArg yonedaEquiv hg
        rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at this
        exact this
      refine ⟨⟨yonedaEquiv g, ?_⟩, ?_⟩
      · change (yonedaEquiv g).val ∈ D.obj (Opposite.op A)
        rw [hgv]
        exact y.property
      · exact Subtype.ext hgv
  have : ∀ A : BigFppfOver B S hS, IsIso ((D.fromPreimage V.ι).app (Opposite.op A)) :=
    fun A => (isIso_iff_bijective _).2 (hbij A)
  exact NatIso.isIso_of_isIso_app (D.fromPreimage V.ι)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback isGrothendieckAbelian_modules

/-- **Shrinking the source to the étale space of an elementary distinguished square.**  Let
`(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square and `E ∈ D(𝒪_X)` supported on the
complement `T` of `U`.  Then `Rf_*E ≅ R(j ≫ f)_*(E|_V)` for every `f : X ⟶ Y`. -/
theorem nonempty_derivedModulePushforward_iso_of_cohomologySupportedOn
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {Y : AlgebraicSpaces B S hS}
    (f : W ⟶ Y) (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    Nonempty ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E ≅
      (Stacks.DerivedFunctor.totalRightDerived
        (modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f))).obj
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)) := by
  let j := edsEtaleHom B S hS hsq
  have hj := isEtale_edsEtaleHom B S hS hsq
  let Rj := Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS j)
  let αj := (Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS j)).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  have : Rj.IsRightDerivedFunctor (Stacks.Injectives.complexUnit (modulePushforward B S hS j) Rj αj)
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
      DerivedCategory.Q Rj _
      (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
        _)).2 fun K hK => by
      have := hK
      exact Stacks.Injectives.isIso_complexUnit_app _ Rj αj K
  let adj := etaleModulePullbackDerivedPushforwardAdjunction B S hS j hj Rj
    (Stacks.Injectives.complexUnit (modulePushforward B S hS j) Rj αj)
  have hη : IsIso (adj.unit.app E) :=
    isIso_unit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adj E hE
  exact ⟨(Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).mapIso
      (asIso (adj.unit.app E)) ≪≫ ((derivedModulePushforwardCompIso B S hS j f).app _).symm⟩

section Main

variable {X Y : AlgebraicSpaces B S hS}

/-- **Perfect direct images.**  Let `S` be a scheme, `Y` a Noetherian algebraic space over `S` and
`f : X ⟶ Y` a morphism of algebraic spaces which is locally of finite type and quasi-separated.
Let `E ∈ D(𝒪_X)` be such that

1. `E ∈ D^b_{Coh}(𝒪_X)`,
2. the support of `Hⁱ(E)` is proper over `Y` for all `i`,
3. `E` has finite tor dimension as an object of `D(f⁻¹𝒪_Y)`.

Then `Rf_*E` is a perfect object of `D(𝒪_Y)`.

`Rf_*` is the total right derived functor of the direct image of modules, and the tor dimension
of `E`, read in `D(f⁻¹𝒪_Y)` by restriction of scalars along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, is measured
against any derived tensor product `T` on `f⁻¹𝒪_Y`-modules (they all agree, being characterized
by their values on K-flat complexes). -/
@[stacks 08IS, sga "6 IV 2.12" "partial"]
theorem isPerfect_derivedModulePushforward_of_hasProperSupport
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E)
    (hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E)))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (inverseImageRingedSite B S hS f))
    (hTor : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u + 1, u, u, u + 1} T
      ((derivedScalarRestriction B S hS f).obj E)) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E) := by
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hE.1
  let Ts : Set.Icc lo hi → Set (points B S hS X.1) := fun i =>
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))
  have hTscl : ∀ i, IsClosed (Ts i) := fun i => (hsupp i).1
  have hT₀p := isProperOver_iUnion B S hS X.2 Y.2 f.hom hf Ts hTscl fun i => (hsupp i).2
  let T₀ := ⋃ i, Ts i
  have hT₀cl : IsClosed T₀ := isClosed_iUnion_of_finite hTscl
  have hEsupp : CohomologySupportedOn B S hS X.1 X.2 T₀ E := by
    intro i
    by_cases h : i ∈ Set.Icc lo hi
    · exact Set.subset_iUnion Ts ⟨i, h⟩
    · have hz : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          E) := by
        simp only [Set.mem_Icc, not_and_or, not_le] at h
        exact h.elim (hlo i) (hhi i)
      exact (le_of_eq ((supportOfSheaf_eq_empty_iff_isZero B S hS X _).2 hz)).trans
        (Set.empty_subset _)
  obtain ⟨V, hV, hVqc, hT₀V⟩ := exists_isQuasiCompactSpace_openSubspace_of_isCompact B S hS X.2 T₀
    (isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf T₀ hT₀cl hT₀p)
  have hsq := isElementaryDistinguishedSquare_openSubspaceOfPoints B S hS X.2 T₀ hT₀cl V hV hT₀V
  have hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 T₀ᶜ) = T₀ := by
    rw [edsComplementPoints, range_pointsMap_ι_openSubspaceOfPoints, compl_compl]
  obtain ⟨eR⟩ := nonempty_derivedModulePushforward_iso_of_cohomologySupportedOn B S hS hsq f E
    (by rw [hcompl]; exact hEsupp)
  let j := edsEtaleHom B S hS hsq
  have hj : IsEtale B S hS j.hom := isEtale_edsEtaleHom B S hS hsq
  let Fj := etaleModulePullback.{u, u} B S hS j hj
  have hf'qc : IsQuasiCompact B S hS (j ≫ f).hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hTop Y.2 hY.2.1 hVqc (j ≫ f).hom
  have hf'qs : IsQuasiSeparated B S hS (j ≫ f).hom :=
    isQuasiSeparated_comp B S hS hsq.isAlgebraicSpace X.2 j.hom f.hom
      (isQuasiSeparated_of_mono B S hS j.hom (inferInstanceAs (Mono V.ι))) hfqs
  obtain ⟨N, hN⟩ := exists_isUniformHigherDirectImageBound B S hS (j ≫ f) hf'qc hf'qs hY.1
  obtain ⟨a, b, hab, hamp⟩ :=
    (Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_iff T _).1 hTor
  obtain ⟨K, hK, hKab, ⟨eK⟩⟩ :=
    Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude T _
      a b hab hamp
  obtain ⟨K', hK', hK'ab, ⟨eK'⟩⟩ :=
    exists_flatRepresentative_etaleModulePullback_comp B S hS j f hj E K hK a b hKab eK
  have hHj : ∀ q : ℤ, (DerivedCategory.homologyFunctor _ q).obj (Fj.mapDerivedCategory.obj E) ≅
      Fj.obj ((DerivedCategory.homologyFunctor _ q).obj E) := fun q =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Fj q).app E
  have hE'qc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj
      (Fj.mapDerivedCategory.obj E)).IsQuasicoherentOnSite := fun q =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso (hHj q).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ hj _ (hE.2 q).toIsQuasicoherentOnSite)
  have : (Fj.mapDerivedCategory.obj E).IsGE lo := by
    rw [DerivedCategory.isGE_iff]
    exact fun q hq => (Fj.map_isZero (hlo q hq)).of_iso (hHj q)
  have hRf := derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport B S hS hTop f hf
    hY E hE hsupp
  obtain ⟨-, ⟨d, hd⟩⟩ := hRf.1
  have := Fact.mk hY.2.2
  refine isPerfect_of_forall_affineChart B S hS Y _ fun W hW => ?_
  obtain ⟨P, hPp, ⟨eP⟩⟩ := isPerfect_etaleModulePullback_chartToSpace_derivedModulePushforward B S
    hS (j ≫ f) W (isNoetherianAffineChart_of_isAffine B S hS Y.1 Y.2 hW) N hN
    (Fj.mapDerivedCategory.obj E) hE'qc lo K' hK' a b hK'ab eK'
    (fun i => isCoherent_of_iso B S hS Y.2 ((DerivedCategory.homologyFunctor _ i).mapIso eR)
      (hRf.2 i))
    d (fun i hi' => (hd i hi').of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eR.symm))
  exact ⟨P, hPp, ⟨eP ≪≫ (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)).mapDerivedCategory.mapIso eR.symm⟩⟩

end Main

end AlgebraicGeometry.Space

end
