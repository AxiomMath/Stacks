module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomStageBijective
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceStages

/-!
# The relative Hom space over an affine base of finite type over `ℤ`

The proof of Stacks 08JY: for a relative Hom situation whose base is Noetherian, choose a perfect
approximation `α : P ⟶ 𝓕[0]` and put `K = Rf_*R𝓗om(P, 𝒢[0])`. The comparison
`AlgebraicGeometry.Space.HomSituation.stageComparison` identifies the functor of Stacks 08JX,
part (2), at `K` with `Hom(𝓕, 𝒢)`, and `K` satisfies the hypotheses of 08JX (2): it is
pseudo-coherent (Stacks 0DKK) and its derived pullbacks have no cohomology in negative degrees,
by the base change of Stacks 08JQ.

## Main results

* `AlgebraicGeometry.Space.HomSituation.stageRelHomIso`: the relative Hom functor of the inverse
  image of modules over the projections `X_T ⟶ X` is the relative Hom functor of Stacks 08JT.
* `HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_approximation`:
  `Hom(𝓕, 𝒢)` is affine and of finite presentation over the base, from a perfect approximation.
* `AlgebraicGeometry.Space.HomSituation.affineFiniteTypeStageRepresentability`: the affine finite
  type case `AlgebraicGeometry.Space.HomSituation.AffineFiniteTypeStageRepresentability`, from
  which Stacks 08K6 follows.

No tag is placed: these are steps of the proof of Stacks 08JY.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleRingedSite_essentiallySmall in
/-- `Rf_*R𝓗om(Q, L)` has no cohomology in negative degrees for `Q` in degrees `≤ 0` and `L` in
degrees `≥ 0`, in the spelling of Stacks 08JQ: `R𝓗om` is left t-exact in the second variable
against such `Q`, and `Rf_*` is left t-exact. -/
theorem isGE_derivedModulePushforward_smallEtaleDerivedSheafHom_of_isLE_of_isGE
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (Q L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hQ : Q.IsLE 0) (hL : L.IsGE 0) :
    ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op Q)).obj L)).IsGE 0 := by
  have h := RingedSite.isGE_derivedSheafHomSmall (smallEtaleRingedSite B S hS X.1 X.2) Q L 0 0
  rw [sub_zero] at h
  exact ⟨(DerivedCategory.TStructure.t.ge 0).prop_of_iso
    (derivedModulePushforwardSheafHomIsoSmall f Q L).symm
    (isGE_derivedModulePushforward_obj B S hS f _ 0 h).ge⟩

namespace HomSituation

variable (v : HomSituation B S hS)

/-- **The relative Hom functor of the inverse image of modules of the small étale topoi over the
projections `X_T ⟶ X` is the relative Hom functor of Stacks 08JT.** -/
def stageRelHomIso :
    (toposPullbackData B S hS).relHomFunctor (toposPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) v.F v.G ≅
      v.homFunctor (modulePushforwardCoherence B S hS) :=
  PullbackData.relHomTransportIso (toposModulePullbackData B S hS)
      (fun f => (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules)
      (fun f => toposPullbackModulesIso f) (toposModulePullbackData_isCoherent B S hS)
      (baseChangeProjectionCone v.f) v.F v.G ≪≫
    (Iso.refl _ : (toposModulePullbackData B S hS).relHomFunctor
        (toposModulePullbackData_isCoherent B S hS) (baseChangeProjectionCone v.f) v.F v.G ≅
      (toposModulePullbackData B S hS).relHomFunctor
        (toposModulePullbackData_isCoherent B S hS) (homTestBaseChangeCone v.f) v.F v.G) ≪≫
    toposModulePullbackDataRelHomIso v.f v.F v.G ≪≫
    (v.homFunctorIsoRelHom (modulePushforwardCoherence B S hS)).symm

variable {Pm : toposDerived B S hS v.X}

/-- The base change map of Stacks 08JQ at a stage is an isomorphism, for `P` perfect, `f`
quasi-compact and quasi-separated and `𝒢` flat over the base (Stacks 08JQ, part (1)). -/
theorem isIso_stageBaseChangeMap
    (hPm : (smallEtaleRingedSite B S hS v.X.1 v.X.2).IsPerfect Pm)
    (hfqc : IsQuasiCompact B S hS v.f.hom) (hfqs : IsQuasiSeparated B S hS v.f.hom)
    (hGfl : IsFlatOver B S hS v.X.2 v.f.hom v.G) (T : v.SchemesOver) :
    IsIso (v.stageBaseChangeMap Pm T (baseChangeInclusion_comp_hom v.f T) rfl) := by
  refine cast (congrArg IsIso (v.stageBaseChangeMap_eq Pm T _ _
    (v.isPullback_baseChangeSquare T).w).symm) ?_
  exact (isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag v.f hfqc hfqs Pm _
    (fun n => (v.single_X_isQuasicoherentOnSite_and_isFlatOver hGfl n).1)
    (fun n => (v.single_X_isQuasicoherentOnSite_and_isFlatOver hGfl n).2)).1 hPm
    ⟨0, fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩ _ _ _
    (v.isPullback_baseChangeSquare T)

/-- **The vanishing hypothesis of Stacks 08JX, part (2), for `K = Rf_*R𝓗om(P, 𝒢[0])`**: for `P`
perfect with all its derived pullbacks in degrees `≤ 0`, `Lg^*K` has no cohomology in negative
degrees over every test scheme, being `Rf_{T*}R𝓗om(Lh^*P, h^*𝒢[0])` by Stacks 08JQ. -/
theorem hasVanishingNegativeDerivedPullback_stage
    (hPm : (smallEtaleRingedSite B S hS v.X.1 v.X.2).IsPerfect Pm)
    (hLE : ∀ {X' : AlgebraicSpaces B S hS} (h : X' ⟶ v.X),
      ((smallEtaleDerivedModulePullback B S hS h).obj Pm).IsLE 0)
    (hfqc : IsQuasiCompact B S hS v.f.hom) (hfqs : IsQuasiSeparated B S hS v.f.hom)
    (hGfl : IsFlatOver B S hS v.X.2 v.f.hom v.G) :
    HasVanishingNegativeDerivedPullback (hasDerivedModulePullbacks B S hS)
      ((smallEtaleDerivedModulePushforward B S hS v.f).obj
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) := by
  intro T i hi
  have := v.isIso_stageBaseChangeMap hPm hfqc hfqs hGfl T
  have hL : (DerivedCategory.Q.obj
      (((modulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G))).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (smallEtaleDegreeZeroTargetIso ((baseChangeProjectionCone v.f).leg T) v.G).symm 0
  have : ((smallEtaleDerivedModulePushforward B S hS ((baseChangeSpacesInclusion v.f).app T)).obj
      (((smallEtaleDerivedSheafHom B S hS ((baseChangeSpaces v.f).obj T)).obj
        (op ((smallEtaleDerivedModulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).obj
          Pm))).obj (DerivedCategory.Q.obj
            (((modulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G))))).IsGE 0 :=
    isGE_derivedModulePushforward_smallEtaleDerivedSheafHom_of_isLE_of_isGE
      ((baseChangeSpacesInclusion v.f).app T)
      ((smallEtaleDerivedModulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).obj Pm)
      (DerivedCategory.Q.obj
        (((modulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)))
      (hLE _) hL
  have hK : ((smallEtaleDerivedModulePullback B S hS ((schemesOverCone v.base).leg T)).obj
      ((smallEtaleDerivedModulePushforward B S hS v.f).obj
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (asIso (v.stageBaseChangeMap Pm T (baseChangeInclusion_comp_hom v.f T) rfl)).symm 0
  exact DerivedCategory.isZero_of_isGE _ 0 i hi (hX := hK)

/-- **The relative Hom space of a stage is affine and of finite presentation over the base**,
from a perfect approximation `α : P ⟶ 𝓕[0]` all of whose derived pullbacks sit in degrees `≤ 0`,
for `f` quasi-compact and quasi-separated, `𝒢` flat over the base and `K = Rf_*R𝓗om(P, 𝒢[0])`
pseudo-coherent: the comparison of Stacks 08JY identifies `Hom(F, G)` with the functor of
Stacks 08JX, part (2), at `K`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_approximation
    (α : Pm ⟶ (DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.F)
    (hiso : ∀ i : ℤ, -1 < i →
      IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) (-1)).map α))
    (hPm : (smallEtaleRingedSite B S hS v.X.1 v.X.2).IsPerfect Pm)
    (hLE : ∀ {X' : AlgebraicSpaces B S hS} (h : X' ⟶ v.X),
      ((smallEtaleDerivedModulePullback B S hS h).obj Pm).IsLE 0)
    (hfqc : IsQuasiCompact B S hS v.f.hom) (hfqs : IsQuasiSeparated B S hS v.f.hom)
    (hGfl : IsFlatOver B S hS v.X.2 v.f.hom v.G)
    (hK : IsPseudoCoherentObject ((smallEtaleDerivedModulePushforward B S hS v.f).obj
      (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))) :
    v.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS) := by
  have := v.isIso_stageComparison α hiso hepi hPm hfqc hfqs hGfl
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_iso
    (asIso (v.stageComparison α hiso hepi) ≪≫ v.stageRelHomIso)
    (isAffineFinitePresentationSectionFunctor_of_hasVanishingNegativeDerivedPullback _ hK
      (v.hasVanishingNegativeDerivedPullback_stage hPm hLE hfqc hfqs hGfl))

/-- **The affine finite type case of Stacks 08JY**: for a situation over `Spec ℤ` whose base is an
affine scheme of finite type over `ℤ`, with `f`, `F`, `G` of finite presentation and `G` flat over
the base with support proper over it, the relative Hom functor is an algebraic space affine and of
finite presentation over the base. The approximation `P ⟶ 𝓕[0]` is perfect since the base is
Noetherian, and `K = Rf_*R𝓗om(P, 𝒢[0])` is pseudo-coherent by Stacks 0DKK. -/
theorem affineFiniteTypeStageRepresentability : AffineFiniteTypeStageRepresentability B := by
  intro T₀ hT₀ v hv hfp hF hG hGfl hprop
  obtain ⟨-, E, hE, α, hiso, hepi, -, hpull⟩ :=
    exists_perfect_approximation_degreeZero_of_stage T₀ hT₀ v hv hfp hF
  have hbase : IsNoetherian B _ _ B.contains_terminal v.base.1 := by
    rw [hv]
    exact isNoetherian_schemeSpace_of_locallyOfFiniteType T₀ hT₀
  have hlft : IsLocallyOfFiniteType B _ _ v.f.hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation _ _ _ hfp.1
  have := hG
  obtain ⟨C, hC, ⟨e⟩⟩ := v.isPseudoCoherent_derivedModulePushforward_smallEtaleDerivedSheafHom
    B.contains_terminal hbase hlft hfp.2.2
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite v.G) hGfl hprop E hE
  refine v.isAffineFinitePresentationAlgebraicSpaceOverBase_of_approximation α hiso hepi hE
    (fun h => (hpull h).1) hfp.2.1 hfp.2.2 hGfl ⟨C, hC, ⟨e ≪≫ ?_⟩⟩
  exact (smallEtaleDerivedModulePushforward B _ _ v.f).mapIso
    (((smallEtaleDerivedSheafHom B _ _ v.X).obj (op E)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app v.G).symm)

end HomSituation

end AlgebraicGeometry.Space

end
