module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitRestrictScalarsIsoAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSectionsLocalModels
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.Homology.Perfect.LocalSplittingDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# `Rf_*𝒪_X = 𝒪_Y ⊕ P` étale locally for proper flat morphisms with good fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.

## Main definitions

* `AlgebraicGeometry.Space.structureModuleIsoModulePushforward`: `𝒪_Y ≅ f_*𝒪_X` as
  `𝒪_Y`-modules when the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is an isomorphism.
* `AlgebraicGeometry.Space.homologyZeroDerivedSectionsDerivedModulePushforwardIso`: over an
  affine base `V = Spec A` with `f♯` invertible, `H⁰(RΓ(V, Rf_*𝒪_X)) ≅ A`.

## References

* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`𝒪_Y ≅ f_*𝒪_X` as `𝒪_Y`-modules** when the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of sheaves
of rings is an isomorphism. -/
def structureModuleIsoModulePushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [IsIso (structureSharp B S hS f)] :
    structureModule Y ≅ (modulePushforward B S hS f).obj (structureModule X) :=
  Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite
    (asIso (structureSharp B S hS f))
    ≪≫ (SheafOfModules.restrictScalars (structureSharp B S hS f)).mapIso
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImage B S hS f)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

section Affine

attribute [local instance 5000] SheafOfModules.instAbelian

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- `Rf_*𝒪_X` has quasi-coherent cohomology for `f` quasi-compact and quasi-separated. -/
theorem qcohDerived_derivedModulePushforward_structureModule
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) :
    QcohDerived B S hS (schemeSpace U)
      ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) :=
  qcohDerived_derivedModulePushforward_obj B S hS f hqc hqs _
    (qcohDerived_singleFunctor_structureModule (B := B) (S := S) (hS := hS) (X := X.1) (hX := X.2))

/-- **`RΓ(V, Rf_*𝒪_X)` lies in degrees `≥ 0`**, over `V = Spec A`. -/
theorem isGE_representedAffineDerivedSections_derivedModulePushforward :
    ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))).IsGE 0 :=
  have := isRightDerivedFunctor_derivedModulePushforward B S hS f
  have := isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f _
    (derivedModulePushforwardUnit B S hS f) (structureModule X)
  isGE_representedAffineDerivedSections_obj B S hS U _ 0

/-- **`H⁰(RΓ(V, Rf_*𝒪_X)) ≅ A`** over `V = Spec A`, for `f` quasi-compact and quasi-separated
with `𝒪_V ⟶ f_*𝒪_X` an isomorphism. -/
def homologyZeroDerivedSectionsDerivedModulePushforwardIso
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    [IsIso (structureSharp B S hS f)] :
    (DerivedCategory.homologyFunctor _ 0).obj
        ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))) ≅
      ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  representedAffineDerivedSectionsHomologyIso B S hS U _
      (qcohDerived_derivedModulePushforward_structureModule B S hS U f hqc hqs) 0 ≪≫
    (representedAffineSections B S hS U).mapIso
      ((derivedModulePushforwardSingleHomologyZeroIso B S hS f).app (structureModule X) ≪≫
        (structureModuleIsoModulePushforward B S hS f).symm ≪≫
        (representedAffineAssociatedObjUnitIso B S hS U).symm) ≪≫
    (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app _)).symm

end Affine

section BaseChange

attribute [local instance 5000] SheafOfModules.instAbelian

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)
  {X X' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (i : X' ⟶ X)

/-- Étale restriction of the structure sheaf is the structure sheaf. -/
def etaleModulePullbackStructureModuleIso (hi : IsEtale B S hS i.hom) :
    (etaleModulePullback.{u, u} B S hS i hi).obj (structureModule X) ≅ structureModule X' :=
  (modulePullbackIsoEtaleModulePullback B S hS i hi).symm.app _ ≪≫
    modulePullbackUnitIso B S hS i

/-- **Étale base change of `Rf_*𝒪`, read in `D(A')`.**  For an étale morphism `U' ⟶ U` of affine
objects with rings `A ⟶ A'` and a cartesian square `X' = U' ×_U X`,
`Rf'_*𝒪_{X'} ≅ Φ_{A'}(RΓ(U, Rf_*𝒪_X) ⊗^L_A A')`, for `f` quasi-compact and quasi-separated. -/
def derivedModulePushforwardStructureModuleBaseChangeIso
    (hg : IsEtale B S hS (representedSpaceMap B S hS g).hom)
    (sq : IsPullback i f' f (representedSpaceMap B S hS g))
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) :
    (derivedModulePushforward B S hS f').obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X')) ≅
      (representedAffineDerivedAssociated B S hS U').obj
        ((representedAffineDerivedExtension B S hS g).functor.obj
          ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))))) :=
  have hi : IsEtale B S hS i.hom :=
    isEtale_of_isPullback B S hS f' i (representedSpaceMap B S hS g) f sq.flip hg
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U _
    (qcohDerived_derivedModulePushforward_structureModule B S hS U f hqc hqs)
  (derivedModulePushforward B S hS f').mapIso
      (((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (etaleModulePullbackStructureModuleIso B S hS i hi)).symm ≪≫
    ((derivedPushforwardEtaleBaseChangeIso B S hS sq hg).app _).symm ≪≫
    ((smallEtaleDerivedModulePullbackIsoEtale B S hS _ hg).app _).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso
      (asIso ((representedAffineDerivedAdjunction B S hS U).counit.app _)).symm ≪≫
    (representedAffineDerivedBaseChangeIso B S hS g).app _

/-- **`Rf_*𝒪 = 𝒪 ⊕ P` on a localization of an affine chart.**  Let `f : X ⟶ Spec A` be
quasi-compact and quasi-separated with `𝒪 ⟶ f_*𝒪_X` invertible, and let `𝔭` be a prime of `A`
at which `K = RΓ(Spec A, Rf_*𝒪_X)` is pseudo-coherent with surjective degree-zero base change map.
Then there is `a ∉ 𝔭` such that over every étale `U' ⟶ Spec A` whose ring is the localization
`A_a`, the base change `f' : X' ⟶ U'` has `Rf'_*𝒪_{X'} ≅ 𝒪 ⊕ P` with `P` strictly perfect in
degrees `≥ 1`. -/
theorem exists_notMem_forall_isStrictlyPerfect_iso_derivedModulePushforward
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    [IsIso (structureSharp B S hS f)] (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    [p.IsPrime]
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))))
    (hbase : StacksDraft.Perfect.CohomologyBaseChangeSurjective.{u, u} p
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))) 0) :
    ∃ a ∉ p, ∀ (U' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ U), IsEtale B S hS (schemeSpaceMap g).hom →
      (letI := (representedAffineCommRingCatHom B S hS g).hom.toAlgebra;
        IsLocalization.Away a Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) →
      ∀ {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ schemeSpace U')
        (i : X' ⟶ X), IsPullback i f' f (schemeSpaceMap g) →
        ∃ P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U')
            (isAlgebraicSpace_yoneda B S hS U')) ℤ,
          IsStrictlyPerfect.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U')
              (isAlgebraicSpace_yoneda B S hS U')).O)) P ∧ P.IsStrictlyGE 1 ∧
          Nonempty ((derivedModulePushforward B S hS f').obj
              ((DerivedCategory.singleFunctor _ 0).obj (structureModule X')) ≅
            (DerivedCategory.singleFunctor _ 0).obj
                (structureModule (schemeSpace U')) ⊞
              DerivedCategory.Q.obj P) := by
  obtain ⟨a, ha, h⟩ := StacksDraft.Perfect.exists_derivedExtension_iso_single_biprod p _ hK
    (isGE_representedAffineDerivedSections_derivedModulePushforward B S hS U f)
    (homologyZeroDerivedSectionsDerivedModulePushforwardIso B S hS U f hqc hqs) hbase
  refine ⟨a, ha, fun U' _ g hg hloc X' f' i sq => ?_⟩
  let := (representedAffineCommRingCatHom B S hS g).hom.toAlgebra
  obtain ⟨P, b, hP1, hPb, hfin, hproj, ⟨e⟩⟩ := h Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
  obtain ⟨P', hP', hP'1, ⟨e'⟩⟩ :=
    exists_strictlyPerfect_iso_representedAffineDerivedAssociated_obj B S hS U' _ P 1 b hP1 hPb
      hfin hproj e
  exact ⟨P', hP', hP'1,
    ⟨derivedModulePushforwardStructureModuleBaseChangeIso B S hS g f f' i hg sq hqc hqs ≪≫ e'⟩⟩

end BaseChange

section Charts

attribute [local instance 5000] SheafOfModules.instAbelian

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

/-- The regular functions on the basic-open chart `D(a)` of an affine étale chart `V` are the
localization of those on `V` away from `a`, along the map induced by the inclusion. -/
theorem isLocalization_away_representedAffineRingHom_openChartInclusion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B S hS F) [IsAffine (chartScheme V)] (a : Γ(chartScheme V, ⊤)) :
    haveI := isAffine_chartScheme_openChart_basicOpen B S hS F V inferInstance a
    letI := (representedAffineCommRingCatHom B S hS ((SmallEtale.toOver B S hS F).map
      (openChartInclusion B S hS F V ((chartScheme V).basicOpen a)))).hom.toAlgebra
    IsLocalization.Away a
      Γ(chartScheme (openChart B S hS F V ((chartScheme V).basicOpen a)), ⊤) := by
  have halg : (representedAffineCommRingCatHom B S hS ((SmallEtale.toOver B S hS F).map
      (openChartInclusion B S hS F V ((chartScheme V).basicOpen a)))).hom.toAlgebra =
      ΓRestrictAlgebra ((chartScheme V).basicOpen a) :=
    congrArg (fun φ => (Scheme.Hom.appTop φ).hom.toAlgebra)
      (toScheme_map_toOver_map_openChartInclusion B S hS F V ((chartScheme V).basicOpen a))
  exact halg ▸ Γ_restrict_isLocalization (chartScheme V) a

variable {X Y : AlgebraicSpaces B S hS}

/-- The base change of `f` to the basic-open chart `D(a)` of a chart `V` is the base change to
`D(a)` of the base change of `f` to `V`. -/
theorem isPullback_pullback_openChartInclusion (f : X ⟶ Y) {V W : SmallEtale B S hS Y.1}
    (ι : W ⟶ V) :
    IsPullback (pullback.lift (pullback.fst f (chartToSpace B S hS Y W))
        (pullback.snd f (chartToSpace B S hS Y W) ≫ chartMap B S hS Y ι)
        (by rw [Category.assoc, chartMap_comp_chartToSpace]; exact pullback.condition))
      (pullback.snd f (chartToSpace B S hS Y W)) (pullback.snd f (chartToSpace B S hS Y V))
      (chartMap B S hS Y ι) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, chartMap_comp_chartToSpace]
  exact IsPullback.of_hasPullback _ _

/-- **`Rf_*𝒪 = 𝒪 ⊕ P` étale locally, from the affine-local inputs.**  Let `f : X ⟶ Y` be such that
its base change `f_V` to every étale chart `V` of `Y` is quasi-compact and quasi-separated with
`𝒪_V ⟶ f_{V*}𝒪` invertible and `Rf_{V*}𝒪` perfect, and such that over every affine chart
`V = Spec A` and prime `𝔭` of `A` the degree-zero base change map of `RΓ(V, Rf_{V*}𝒪)` at `𝔭` is
surjective.  Then every chart `U` of `Y` has a covering family of charts `V` over which
`Rf_{V*}𝒪 ≅ 𝒪 ⊕ P` with `P` strictly perfect in degrees `≥ 1`. -/
theorem exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_affine (f : X ⟶ Y)
    (hqc : ∀ V : SmallEtale B S hS Y.1,
      IsQuasiCompact B S hS (pullback.snd f (chartToSpace B S hS Y V)).hom)
    (hqs : ∀ V : SmallEtale B S hS Y.1,
      IsQuasiSeparated B S hS (pullback.snd f (chartToSpace B S hS Y V)).hom)
    (hsharp : ∀ V : SmallEtale B S hS Y.1,
      IsIso (structureSharp B S hS (pullback.snd f (chartToSpace B S hS Y V))))
    (hperf : ∀ (V : SmallEtale B S hS Y.1),
      (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).IsPerfect
        ((derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (structureModule (pullback f (chartToSpace B S hS Y V))))))
    (hbase : ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
      (p : Ideal Γ(chartScheme V, ⊤)) [p.IsPrime],
        StacksDraft.Perfect.CohomologyBaseChangeSurjective.{u, u} p
          ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS Y.1).obj V)).obj
            ((derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (structureModule (pullback f (chartToSpace B S hS Y V)))))) 0)
    (U : SmallEtale B S hS Y.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 U ∧
      ∀ ⦃V : SmallEtale B S hS Y.1⦄ (g : V ⟶ U), R g →
        ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2) ℤ,
          IsStrictlyPerfect.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
                (chartSpace B S hS Y V).2).O)) P ∧ P.IsStrictlyGE 1 ∧
          Nonempty ((derivedModulePushforward B S hS
              (pullback.snd f (chartToSpace B S hS Y V))).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  (structureModule (pullback f (chartToSpace B S hS Y V)))) ≅
            (DerivedCategory.singleFunctor _ 0).obj (structureModule (chartSpace B S hS Y V)) ⊞
              DerivedCategory.Q.obj P) := by
  refine ⟨_, ?_, fun _ _ h => h⟩
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨W, hW, hxW, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (chartScheme U).isBasis_affineOpens
      (show x ∈ (⊤ : (chartScheme U).Opens) from trivial)
  let VW := openChart B S hS Y.1 U W
  have : IsAffine (chartScheme VW) := hW
  have : IsIso (structureSharp B S hS (X := pullback f (chartToSpace B S hS Y VW))
      (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj VW),
        isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj VW)⟩)
      (pullback.snd f (chartToSpace B S hS Y VW))) := hsharp VW
  let x' : chartScheme VW := ⟨x, hxW⟩
  let p := ((chartScheme VW).toSpecΓ x').asIdeal
  have hK := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
    (isPerfect_representedAffineDerivedSections_obj B S hS ((SmallEtale.toOver B S hS Y.1).obj VW)
      _ (hperf VW))
  obtain ⟨a, ha, h⟩ := exists_notMem_forall_isStrictlyPerfect_iso_derivedModulePushforward B S hS
    (U := (SmallEtale.toOver B S hS Y.1).obj VW) (pullback.snd f (chartToSpace B S hS Y VW))
    (hqc VW) (hqs VW) p hK (hbase VW p)
  let ι := openChartInclusion B S hS Y.1 VW ((chartScheme VW).basicOpen a)
  have : IsAffine (chartScheme (openChart B S hS Y.1 VW ((chartScheme VW).basicOpen a))) :=
    isAffine_chartScheme_openChart_basicOpen B S hS Y.1 VW inferInstance a
  obtain ⟨P, hP, hP1, ⟨e⟩⟩ := h _ ((SmallEtale.toOver B S hS Y.1).map ι)
    (isEtale_chartMap B S hS Y ι)
    (isLocalization_away_representedAffineRingHom_openChartInclusion B S hS VW a)
    (pullback.snd f (chartToSpace B S hS Y _)) _
    (isPullback_pullback_openChartInclusion B S hS f ι)
  have hxa : x' ∈ (chartScheme VW).basicOpen a := by
    rwa [← Scheme.toSpecΓ_preimage_basicOpen]
  refine ⟨_, ι ≫ openChartInclusion B S hS Y.1 U W,
    Sieve.le_generate _ _ _ ⟨P, hP, hP1, ⟨e⟩⟩, ⟨⟨x', hxa⟩, ?_⟩⟩
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_toOver_map_openChartInclusion,
    toScheme_map_toOver_map_openChartInclusion]
  rfl

/-- Under the hypotheses of Stacks 0E6B, the base change of `f` to every étale chart of `Y` is
quasi-compact and quasi-separated with invertible structure map. -/
theorem isQuasiCompact_and_isQuasiSeparated_and_isIso_structureSharp_pullback_snd (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p))))
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    IsQuasiCompact B S hS (pullback.snd f g).hom ∧ IsQuasiSeparated B S hS (pullback.snd f g).hom ∧
      IsIso (structureSharp B S hS (pullback.snd f g)) := by
  have hg : IsProper B S hS (pullback.snd f g).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback (IsPullback.of_hasPullback f g) hf
  exact ⟨hg.2.1.2, isQuasiSeparated_of_isSeparated B S hS hg.1,
    (isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B S hS f hf hfl hfp h).2 _ g⟩

end Charts

end AlgebraicGeometry.Space

end
