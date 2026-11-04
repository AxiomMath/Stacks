module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.SchemeOpenRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuasicoherentHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.AboveTheDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections

/-!
# Vanishing above the dimension: the induction along elementary distinguished squares

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S` with
`dim X ≤ d`, and let `F` be a quasi-coherent `𝒪_X`-module.  Clause (1) of Stacks 0A4R says
that `Hᑫ(X, F) = 0` for `q > d`.  This file runs the induction principle of Stacks 08GP for
that statement.  On an affine object the higher cohomology of a quasi-coherent module vanishes;
across an elementary distinguished square `(U ⊆ W, V ⟶ W)` with `V` affine and intersection
`P = U ×_W V`, the Mayer–Vietoris sequence gives `Hⁿ⁺¹(W, F) = 0` from `Hⁿ⁺¹(U, F)`,
`Hⁿ⁺¹(V, F)` and `Hⁿ(P, F)`.  For `n > d` the last group vanishes by induction; for
`n = d ≥ 1` it vanishes because `P` is a quasi-compact open subspace of the affine space `V`,
whose dimension is at most `d` since `V` is étale over `X`, and on a quasi-compact open of an
affine scheme of dimension at most `d` the Zariski cohomology vanishes in degree `d`
(clause (2) of Stacks 0A3G).  For `n = d = 0` the group `H⁰(P, F)` need not vanish; instead,
in dimension zero the quasi-compact open `U` is closed, and the square is replaced by the one
formed by `U` and its complement, whose intersection is empty.

## Main results

* `AlgebraicGeometry.isZero_hgroup_of_isAffine_of_topologicalKrullDim_le`: on an affine scheme of
  dimension at most `d`, a quasi-coherent module has no cohomology over a quasi-compact open in
  any positive degree at least `d`.
* `AlgebraicGeometry.isZero_hgroup_of_isOpenImmersion_of_isAffine`: the same for a
  quasi-compact scheme with an open immersion into such an affine scheme.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_schemeSpace_of_isZero_hgroup`:
  on a represented algebraic space the cohomology of a quasi-coherent module vanishes with the
  Zariski cohomology of the scheme.
* `Space.isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace`: on a
  quasi-compact open subspace of an affine algebraic space of dimension at most `d` the
  cohomology of a quasi-coherent module vanishes in every positive degree at least `d`.
* `AlgebraicGeometry.Space.dimension_le_of_isEtale`: an étale morphism does not raise the
  dimension.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_iff`: the cohomology of a module
  vanishes as a module over the global functions exactly when it vanishes as an abelian group.
* `AlgebraicGeometry.Space.isZero_modules_of_isEmpty_points`: a module on an algebraic space
  with no points is zero.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_of_compl_subset`: an open subspace
  and an open immersion covering an algebraic space form an elementary distinguished square, and
  `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_of_range_subset`: the open part of an
  elementary distinguished square can be enlarged.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_of_dimension_le`: the induction,
  that is clause (1) of Stacks 0A4R for a natural number `d`, with values in abelian groups.

## References

* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry

/-! ### The Zariski input: quasi-compact opens of an affine scheme -/

section Zariski

/-- **The cohomology of a quasi-coherent module on a quasi-compact open of an affine scheme
vanishes in every positive degree at least the dimension.**  Let `X` be an affine scheme with
`dim X ≤ d`, `U ⊆ X` a quasi-compact open and `F` a quasi-coherent `𝒪_X`-module.  Then
`Hᑫ(U, F) = 0` for `q ≥ d`, `q > 0`.

The underlying space of `X` is spectral, so by clause (2) of Stacks 0A3G the restriction
`Hᑫ(X, F) ⟶ Hᑫ(U, F)` is onto, and `Hᑫ(X, F) = 0` by Stacks 01XB. -/
theorem isZero_hgroup_of_isAffine_of_topologicalKrullDim_le
    (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (d q : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hdq : d ≤ q) (hq : 0 < q) :
    IsZero (Hgroup X.ringCatSheaf U q F) := by
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    Stacks.Topology.hasExt_sheafOpens X
  have : SpectralSpace X := spectralSpace_of_compactSpace_of_quasiSeparatedSpace X
  rw [Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf]
  have h0 := (Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf ⊤ F
    q).1 (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine (X := X) F q hq)
  have : Epi ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf q).map
      (homOfLE (show U ≤ ⊤ from le_top)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).2 <|
      Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q
        (hdim.trans (by exact_mod_cast hdq)) U hU
  exact IsZero.of_epi ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf q).map
    (homOfLE (show U ≤ ⊤ from le_top)).op) h0

/-- **The cohomology of a quasi-coherent module on a quasi-compact scheme with an open immersion
into an affine scheme vanishes in every positive degree at least the dimension of the target.**
Let `g : Y ⟶ X` be an open immersion with `Y` quasi-compact and `X` affine with `dim X ≤ d`, and
let `F` be a quasi-coherent `𝒪_Y`-module.  Then `Hᑫ(Y, F) = 0` for `q ≥ d`, `q > 0`.

`Y` is isomorphic to the open subscheme `W = g(Y)` of `X`, and cohomology does not change along
that isomorphism; over `W` the module is the restriction of `g_*F`, which is quasi-coherent by
Stacks 01LC, and the cohomology of the restriction is the cohomology over `W` of `g_*F`
(Stacks 01E1), which vanishes by
`AlgebraicGeometry.isZero_hgroup_of_isAffine_of_topologicalKrullDim_le`. -/
theorem isZero_hgroup_of_isOpenImmersion_of_isAffine
    {Y X : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] [IsAffine X]
    [CompactSpace Y] (F : Y.Modules) [F.IsQuasicoherent] (d q : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdq : d ≤ q) (hq : 0 < q) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ q F) := by
  let W := g.opensRange
  let φ : Y ≅ W.toScheme := g.isoOpensRange
  have hW : IsCompact (W : Set X) := by
    simpa [W] using isCompact_range g.continuous
  have hz : IsZero (Hgroup X.ringCatSheaf W q ((Scheme.Modules.pushforward g).obj F)) :=
    isZero_hgroup_of_isAffine_of_topologicalKrullDim_le X _ W hW d q hdim hdq hq
  have e0 : (Scheme.Modules.pushforward g).obj F ≅
      (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pushforward φ.hom).obj F) :=
    (Scheme.Modules.pushforwardCongr (Scheme.Hom.isoOpensRange_hom_ι g).symm).app F ≪≫
      (Scheme.Modules.pushforwardComp φ.hom W.ι).app F
  have e1 : (Scheme.Modules.restrictFunctor W.ι).obj ((Scheme.Modules.pushforward g).obj F) ≅
      (Scheme.Modules.pushforward φ.hom).obj F :=
    (Scheme.Modules.restrictFunctor W.ι).mapIso e0 ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app _
  have h3 : IsZero (Hgroup W.toScheme.ringCatSheaf ⊤ q
      ((Scheme.Modules.restrictFunctor W.ι).obj ((Scheme.Modules.pushforward g).obj F))) :=
    hz.of_iso ((Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso X W q).app
      ((Scheme.Modules.pushforward g).obj F)).symm
  have h4 : IsZero (Hgroup W.toScheme.ringCatSheaf ⊤ q
      ((Scheme.Modules.pushforward φ.hom).obj F)) :=
    h3.of_iso ((Hfunctor W.toScheme.ringCatSheaf ⊤ q).mapIso e1.symm)
  exact (Stacks.Cohomology.ClosedImmersion.hgroupPushforwardIso φ.hom F q).isZero_iff.2 h4

end Zariski

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-! ### Cohomology on a represented algebraic space -/

/-- **The cohomology of a quasi-coherent module on a represented algebraic space vanishes with
the Zariski cohomology of the scheme.**  Let `T` be an object of the site and `M` a
quasi-coherent module on the algebraic space `yoneda T`.  If `Hⁿ(T, 𝓕) = 0` for every
quasi-coherent `𝒪_T`-module `𝓕`, for some `n > 0`, then `Hⁿ(yoneda T, M) = 0`.

The module `M` is associated with a quasi-coherent `𝒪_T`-module, by the equivalence of
Stacks 03DX; over the identity chart, which is terminal, the étale cohomology of an associated
module vanishes with the Zariski cohomology
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup`); and
global sections are sections over the terminal chart. -/
theorem isZero_rightDerived_globalSectionsFunctor_schemeSpace_of_isZero_hgroup
    (T : BigFppfOver B S hS) (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n)
    (h : ∀ F : ((BigFppfOver.toScheme B S hS).obj T).Modules, SheafOfModules.IsQuasicoherent F →
      IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf ⊤ n F)) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O)).rightDerived n).obj
        M) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O
  let X : (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ := Opposite.op (idEtaleChart B S hS T)
  have hX : IsInitial X := (isTerminalIdEtaleChart B S hS T).op
  let e := globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O X hX
  have : (SheafOfModules.evaluation O X).Additive := ⟨fun {_ _ _ _} => rfl⟩
  let E := representedQuasicoherentSchemeEquivalence B S hS T
  let F := E.inverse.obj ⟨M, hM⟩
  have hM' : ((E.functor.obj F).obj) ≅ M :=
    (ObjectProperty.ι _).mapIso (E.counitIso.app ⟨M, hM⟩)
  have h0 : IsZero (((SheafOfModules.evaluation O X).rightDerived n).obj M) :=
    (isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup B S hS T F.obj F.property n hn
      (h F.obj F.property)).of_iso
        (((SheafOfModules.evaluation O X).rightDerived n).mapIso hM').symm
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived n).obj M)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) n).app
            M).symm ≪≫
        (ModuleSheafCohomology.rightDerivedIso e n).app M ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O X)
            (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) n).app M)
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 h1)

/-- **An étale morphism does not raise the dimension**: the dimension at a point is preserved
by an étale morphism (Stacks 0A4H), and the dimension is the supremum of these. -/
theorem dimension_le_of_isEtale {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsEtale B S hS f) : dimension B S hS X hX ≤ dimension B S hS Y hY :=
  iSup_le fun x => (dimensionAtPoint_eq_of_isEtale B S hS hX hY f hf x).trans_le
    (le_iSup (dimensionAtPoint B S hS Y hY) _)

/-- The cohomology of a module on an algebraic space vanishes as an abelian group exactly when
it vanishes as a module over the global functions: the forgetful functor is exact and faithful,
so it commutes with the right derived functors and reflects zero objects. -/
theorem isZero_rightDerived_globalSectionsAb_iff (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    IsZero (((globalSectionsAb B S hS X).rightDerived q).obj F) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj F) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let e := (Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
    (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) q).app F
  exact ⟨fun h => _root_.isZero_of_faithful (forget₂ _ AddCommGrpCat.{u + 1}) (h.of_iso e.symm),
    fun h => (Functor.map_isZero (forget₂ _ AddCommGrpCat.{u + 1}) h).of_iso e⟩

/-- **The cohomology of a quasi-coherent module on a quasi-compact open subspace of an affine
algebraic space vanishes in every positive degree at least the dimension.**  Let `V` be an affine
algebraic space with `dim V ≤ d`, `i : P ⟶ V` an open immersion with `P` quasi-compact and `N` a
quasi-coherent `𝒪_P`-module.  Then `Hᑫ(P, N) = 0` for `q ≥ d`, `q > 0`.

Write `V ≅ T` with `T` an affine scheme.  The open immersion `P ⟶ T` is representable by an
open immersion of schemes `T' ⟶ T`, so `P ≅ T'`; cohomology of quasi-coherent modules does
not change along that isomorphism (Stacks 0D2U), and on the represented space `T'` it vanishes
with the Zariski cohomology of `T'`, which is
`AlgebraicGeometry.isZero_hgroup_of_isOpenImmersion_of_isAffine`.  The dimension of `T` is that
of `V`, an isomorphism being étale. -/
theorem isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace
    {V P : AlgebraicSpaces B S hS} (i : P ⟶ V) (hi : IsOpenImmersion B S hS i.hom)
    (hV : IsAffineSpace B S hS V.1) (d q : ℕ) (hdim : dimension B S hS V.1 V.2 ≤ d)
    (hdq : d ≤ q) (hq : 0 < q) (hP : IsQuasiCompactSpace B S hS P.1)
    (N : Modules.{u, u} B S hS P.1 P.2) (hN : N.IsQuasicoherentOnSite) :
    IsZero (((globalSectionsAb B S hS P).rightDerived q).obj N) := by
  obtain ⟨T, hT, ⟨eV⟩⟩ := hV
  have hi' : IsOpenImmersion B S hS (i.hom ≫ eV.hom) :=
    isOpenImmersion_comp B S hS _ _ hi (isOpenImmersion_of_isIso B S hS eV.hom)
  let T' := hi'.rep.pullback (𝟙 (yoneda.obj T))
  let g : T' ⟶ T := hi'.rep.snd (𝟙 (yoneda.obj T))
  have hg : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g) :=
    hi'.property_snd (𝟙 (yoneda.obj T))
  have : IsIso (hi'.rep.fst (𝟙 (yoneda.obj T))) :=
    (hi'.rep.isPullback (𝟙 (yoneda.obj T))).isIso_fst_of_isIso
  let e : yoneda.obj T' ≅ P.1 := asIso (hi'.rep.fst (𝟙 (yoneda.obj T)))
  have hT'c : CompactSpace ((BigFppfOver.toScheme B S hS).obj T') :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (IsQuasiCompactSpace.of_iso B S hS hP e.symm)
  have hdimT : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj T) ≤ (d : WithBot ℕ∞) := by
    rw [← dimension_yoneda_eq_topologicalKrullDim B S hS T]
    exact (dimension_le_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS T) V.2 eV.inv
      (isEtale_of_isIso B S hS _)).trans hdim
  let f : P ⟶ schemeSpace T' := ObjectProperty.homMk e.inv
  have haff : IsAffineHom B S hS f.hom := isAffineHom_of_isIso (f := e.inv)
  have hz := isZero_rightDerived_globalSectionsFunctor_schemeSpace_of_isZero_hgroup B S hS T'
    ((modulePushforward B S hS f).obj N)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional _ _ _ f haff _ hN) q hq
    (fun G _ => isZero_hgroup_of_isOpenImmersion_of_isAffine
      ((BigFppfOver.toScheme B S hS).map g) G d q hdimT hdq hq)
  rw [isZero_rightDerived_globalSectionsAb_iff]
  exact _root_.isZero_of_faithful (forget₂ _ AddCommGrpCat.{u + 1})
    ((Functor.map_isZero (forget₂ _ AddCommGrpCat.{u + 1}) hz).of_iso
      (cohomologyIsoOfIsAffineHom B S hS f haff N hN q))

/-- **In dimension at most zero a quasi-compact open subspace is closed.**  Let `W` be a
quasi-compact quasi-separated algebraic space with `dim W ≤ 0` and `U ⊆ W` a quasi-compact open
subspace.  Then the point set of `U` is closed in `|W|`.

The space `|W|` is spectral (Stacks 0A4G) of Krull dimension `dim W` (Stacks 0A4J), so it is
empty or profinite, hence Hausdorff, and the compact set `|U|` is closed. -/
theorem isClosed_range_pointsMap_ι_of_dimension_le_zero {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hWqc : IsQuasiCompactSpace B S hS W)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W)
    (hdim : dimension B S hS W hW ≤ 0) (U : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    IsClosed (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
  have : SpectralSpace (points B S hS W) :=
    spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated B S hS W hW hWqc hWqs
  have hk : topologicalKrullDim (points B S hS W) ≤ 0 :=
    (topologicalKrullDim_points_eq_dimension_of_isDecentSpace B S hS hW
      (isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS W hW hWqs)).trans_le hdim
  have : CompactSpace (points B S hS U.toFunctor) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS hU.1 hUqc
  have hc : IsCompact (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isCompact_range (continuous_pointsMap B S hS U.ι)
  rcases isEmpty_or_nonempty (points B S hS W) with h | h
  · simp [Set.eq_empty_of_isEmpty]
  · have h0 : topologicalKrullDim (points B S hS W) = 0 :=
      le_antisymm hk (by
        obtain ⟨x⟩ := h
        have : Nonempty (TopologicalSpace.IrreducibleCloseds (points B S hS W)) :=
          ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
        exact Order.krullDim_nonneg)
    have := ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).1
      (Stacks.CohomologyVanishing.isProfiniteStacks_of_topologicalKrullDim_eq_zero h0)).2.1
    exact hc.isClosed

/-- **An open subspace and an open immersion covering an algebraic space form an elementary
distinguished square.**  If `U` is an open subspace of `W` and `g : V ⟶ W` an open immersion
from an algebraic space whose point set contains `|W| ∖ |U|`, then `(U ⊆ W, g)` is an
elementary distinguished square: the reduced closed subspace on `|W| ∖ |U|` factors through the
image of `g` (Stacks 03IE), hence through `g`, and `g` being a monomorphism it is an
isomorphism over it. -/
theorem isElementaryDistinguishedSquare_of_compl_subset {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    (hV : IsAlgebraicSpace B S hS V) (g : V ⟶ W) (hg : IsOpenImmersion B S hS g)
    (h : (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ ⊆
      Set.range (pointsMap B S hS V g)) :
    IsElementaryDistinguishedSquare B S hS hW U g := by
  have _ : Mono g := mono_of_presheaf_isOpenImmersion hg
  have hcl : IsClosed (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
    (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hW U hU).isClosed_compl
  refine ⟨hV, hU, isEtale_of_isOpenImmersion B S hS hg, hcl, ?_⟩
  set T := reducedClosedSubspace B S hS W hW _ hcl
  have hTalg := isAlgebraicSpace_reducedClosedSubspace B S hS W hW _ hcl
  have hQ := isOpenSubspace_range_of_isAlgebraicSpace B S hS hV g hg
  obtain ⟨t, ht⟩ := (factorsThrough_openSubspace_iff_points B S hS hW hTalg
    (Subfunctor.range g) hQ T.ι).2 (by
      rw [range_pointsMap_ι_reducedClosedSubspace]
      refine h.trans ?_
      rintro _ ⟨v, rfl⟩
      refine ⟨pointsMap B S hS _ (Subfunctor.toRange g) v, ?_⟩
      rw [← pointsMap_comp_apply, Subfunctor.toRange_ι])
  let t' : T.toFunctor ⟶ V := t ≫ inv (Subfunctor.toRange g)
  have e1 : inv (Subfunctor.toRange g) ≫ g = (Subfunctor.range g).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have hg' : t' ≫ g = T.ι := by
    change (t ≫ inv (Subfunctor.toRange g)) ≫ g = T.ι
    rw [Category.assoc, e1, ht]
  have sq := Subfunctor.isPullback_preimage g T
  refine ⟨⟨sq.lift (𝟙 _) t' (by simp [hg']), ?_, sq.lift_fst _ _ _⟩⟩
  apply sq.hom_ext
  · simp
  · rw [← cancel_mono g]
    simp only [Category.assoc, sq.lift_snd, hg', Category.id_comp]
    exact sq.w

/-- **Enlarging the open part of an elementary distinguished square.**  If `(U ⊆ W, f : V ⟶ W)`
is an elementary distinguished square and `U'` is an open subspace of `W` whose point set
contains that of `U`, then `(U' ⊆ W, f)` is an elementary distinguished square: the reduced
closed subspace on `|W| ∖ |U'|` lies in the one on `|W| ∖ |U|` (Stacks 03IE), and `f`, an
isomorphism over the larger one, is an isomorphism over the smaller one, by base change. -/
theorem isElementaryDistinguishedSquare_of_range_subset {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hW : IsAlgebraicSpace B S hS W} {U : Subfunctor W} {f : V ⟶ W}
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (U' : Subfunctor W)
    (hU' : IsOpenSubspace B S hS U')
    (hle : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS U'.toFunctor U'.ι)) :
    IsElementaryDistinguishedSquare B S hS hW U' f := by
  have hcl : IsClosed (Set.range (pointsMap B S hS U'.toFunctor U'.ι))ᶜ :=
    (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hW U' hU').isClosed_compl
  refine ⟨hsq.isAlgebraicSpace, hU', hsq.isEtale, hcl, ?_⟩
  set T := reducedClosedSubspace B S hS W hW
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement with hT
  set T' := reducedClosedSubspace B S hS W hW _ hcl
  have hT'alg := isAlgebraicSpace_reducedClosedSubspace B S hS W hW _ hcl
  have hT'red := hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS W hW _ hcl
  obtain ⟨g, hg⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS W hW
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement hT'alg hT'red
    T'.ι).2 (by
      rw [range_pointsMap_ι_reducedClosedSubspace]
      exact Set.compl_subset_compl.2 hle)
  have hTiso : IsIso (T.fromPreimage f) := by
    rw [hT]
    exact hsq.isIsoOverComplement
  have sqT := Subfunctor.isPullback_preimage f T
  have sqT' := Subfunctor.isPullback_preimage f T'
  have hw : (T'.fromPreimage f ≫ g) ≫ T.ι = (T'.preimage f).ι ≫ f := by
    rw [Category.assoc, hg]
    exact sqT'.w
  have hSmall : IsPullback (sqT.lift _ _ hw) (T'.fromPreimage f) (T.fromPreimage f) g := by
    refine IsPullback.of_right ?_ (sqT.lift_fst _ _ hw) sqT.flip
    rw [sqT.lift_snd, hg]
    exact sqT'.flip
  exact hSmall.isIso_snd_of_isIso

/-- A fibre product of two morphisms whose images in the point space are disjoint has no
points. -/
theorem isEmpty_points_pullback_of_disjoint {A C W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : A ⟶ W) (g : C ⟶ W)
    (h : Disjoint (Set.range (pointsMap B S hS A f)) (Set.range (pointsMap B S hS C g))) :
    IsEmpty (points B S hS (pullback f g)) :=
  ⟨fun x => Set.disjoint_left.1 h ⟨pointsMap B S hS _ (pullback.fst f g) x, rfl⟩
    ⟨pointsMap B S hS _ (pullback.snd f g) x, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition]⟩⟩

/-- **A module on an algebraic space with no points is zero**: every étale chart of such a space
has empty underlying scheme, so it is covered by the empty sieve, and the sections of a sheaf
over it vanish. -/
theorem isZero_modules_of_isEmpty_points (X : AlgebraicSpaces B S hS)
    (hX : IsEmpty (points B S hS X.1)) (M : Modules.{u, u} B S hS X.1 X.2) : IsZero M := by
  refine _root_.isZero_of_faithful (SheafOfModules.toSheaf _) ?_
  refine _root_.isZero_of_faithful (sheafToPresheaf _ _) ?_
  refine Functor.isZero _ fun V => ?_
  refine CategoryTheory.Sheaf.isZero_obj_of_bot_mem
    ((SheafOfModules.toSheaf _).obj M) (V := V.unop) ?_
  refine SmallEtale.bot_mem_topology B S hS X.1 _ ⟨fun x => hX.false ?_⟩
  exact pointsMap B S hS _ V.unop.obj.hom ((schemePointsHomeomorph B S hS _).symm x)

/-- On an algebraic space with no points every cohomology group of every module vanishes. -/
theorem isZero_rightDerived_globalSectionsAb_of_isEmpty_points (X : AlgebraicSpaces B S hS)
    (hX : IsEmpty (points B S hS X.1)) (M : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    IsZero (((globalSectionsAb B S hS X).rightDerived q).obj M) :=
  Functor.map_isZero _ (isZero_modules_of_isEmpty_points B S hS X hX M)

/-- If `H^n` vanishes on quasi-coherent modules over `Y`, it vanishes for the restriction along an
étale `j : Y ⟶ W` of a quasi-coherent module on `W`, read on `W`. -/
private theorem isZero_restrictPush_of_forall_isQuasicoherentOnSite {Y W : AlgebraicSpaces B S hS}
    (j : Y ⟶ W) (hj : IsEtale B S hS j.hom) (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ)
    (h : ∀ G : Modules.{u, u} B S hS Y.1 Y.2, G.IsQuasicoherentOnSite →
      IsZero (((globalSectionsAb B S hS Y).rightDerived n).obj G)) :
    IsZero ((((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
        globalSectionsAb B S hS W).rightDerived n).obj F) :=
  (h _ (isQuasicoherentOnSite_etaleModulePullback B S hS j hj F hF)).of_iso
    (rightDerivedGlobalSectionsAbRestrictPushIso B S hS j hj F n)

/-- **The degree-one step of the induction in dimension zero.**  Let `(U ⊆ W, f : V ⟶ W)` be an
elementary distinguished square with `W` quasi-compact quasi-separated of dimension at most `0`,
`U` quasi-compact and `V` affine, and suppose that `H¹(U, -)` vanishes on quasi-coherent modules.
Then `H¹(W, F) = 0` for every quasi-coherent `𝒪_W`-module `F`.

In dimension zero `|U|` is closed (`isClosed_range_pointsMap_ι_of_dimension_le_zero`), so its
complement is the point set of an open subspace `U'`, and `(U ⊆ W, U' ⟶ W)` is an elementary
distinguished square whose intersection has no points; Mayer–Vietoris reduces the claim to
`H¹(U', F) = 0`.  Over `U'` the base change of the given square has an open part with no points,
an intersection with no points, and étale part `f⁻¹(U')`, a quasi-compact open subspace of the
affine `V` of dimension at most `0`, where `H¹` vanishes by
`isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace`. -/
theorem isZero_rightDerived_globalSectionsAb_one_of_eds_of_dimension_le_zero
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor W.1}
    {f : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hdim : dimension B S hS W.1 W.2 ≤ 0) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hV : IsAffineSpace B S hS V)
    (hU1 : ∀ G : Modules.{u, u} B S hS U.toFunctor hsq.isOpenSubspace.1,
      G.IsQuasicoherentOnSite → IsZero (((globalSectionsAb B S hS
        ⟨U.toFunctor, hsq.isOpenSubspace.1⟩).rightDerived 1).obj G))
    (F : Modules.{u, u} B S hS W.1 W.2) (hF : F.IsQuasicoherentOnSite) :
    IsZero (((globalSectionsAb B S hS W).rightDerived 1).obj F) := by
  have hUo := hsq.isOpenSubspace
  have hcl := isClosed_range_pointsMap_ι_of_dimension_le_zero B S hS W.2 hWqc hWqs hdim U hUo hUqc
  -- the complementary open subspace
  let U'o := (openSubspacesOrderIso B S hS W.1 W.2).symm
    ⟨(Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ, hcl.isOpen_compl⟩
  let U' : Subfunctor W.1 := U'o.1
  have hU' : IsOpenSubspace B S hS U' := U'o.2
  have hU'range : Set.range (pointsMap B S hS U'.toFunctor U'.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ := by
    rw [← openSubspacesOrderIso_apply B S hS W.1 W.2 U'o]
    simp [U'o]
  have hsq1 := isElementaryDistinguishedSquare_of_compl_subset B S hS W.2 U hUo hU'.1 U'.ι
    hU'.2 hU'range.ge
  have hdisj : Disjoint (Set.range (pointsMap B S hS U.toFunctor U.ι))
      (Set.range (pointsMap B S hS U'.toFunctor U'.ι)) := by
    rw [hU'range]
    exact disjoint_compl_right
  refine isZero_rightDerived_globalSectionsAb_succ_of_eds B S hS hsq1 F 0 ?_ ?_ ?_
  · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
      (isEtale_edsOpenHom B S hS hsq1) F hF 1 hU1
  · refine isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
      (isEtale_edsEtaleHom B S hS hsq1) F hF 1 fun G hG => ?_
    -- `H¹(U', F|_{U'}) = 0`, along the base change of the square to `U'`
    let W' : AlgebraicSpaces B S hS := ⟨U'.toFunctor, hU'.1⟩
    have hsq2 : IsElementaryDistinguishedSquare B S hS W'.2 (U.preimage U'.ι)
        (pullback.snd f U'.ι) :=
      isElementaryDistinguishedSquare_preimage B S hS W.2 hU'.1 U f hsq U'.ι
    have hempty2 : IsEmpty (points B S hS (U.preimage U'.ι).toFunctor) := ⟨fun x =>
      Set.disjoint_left.1 hdisj ⟨pointsMap B S hS _ (U.fromPreimage U'.ι) x, rfl⟩
        ⟨pointsMap B S hS _ (U.preimage U'.ι).ι x, by
          rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]⟩⟩
    have hU'qc : IsQuasiCompactSpace B S hS U'.toFunctor := by
      have : CompactSpace (points B S hS W.1) :=
        compactSpace_points_of_isQuasiCompactSpace B S hS W.2 hWqc
      refine isQuasiCompactSpace_of_isCompact_range B S hS W.2 hU' ?_
      rw [hU'range]
      exact (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS W.2 U hUo).isClosed_compl.isCompact
    refine isZero_rightDerived_globalSectionsAb_succ_of_eds B S hS
      (W := W') hsq2 G 0 ?_ ?_ ?_
    · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsOpenHom B S hS hsq2) G hG 1
        fun _ _ => isZero_rightDerived_globalSectionsAb_of_isEmpty_points B S hS _ hempty2 _ 1
    · refine isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsEtaleHom B S hS hsq2) G hG 1 fun N hN => ?_
      let VA : AlgebraicSpaces B S hS := ⟨V, hsq.isAlgebraicSpace⟩
      let i : edsEtale B S hS hsq2 ⟶ VA := ObjectProperty.homMk (pullback.fst f U'.ι)
      have hsqA : IsPullback (ObjectProperty.homMk (pullback.snd f U'.ι) :
            edsEtale B S hS hsq2 ⟶ W') i
          (ObjectProperty.homMk U'.ι : W' ⟶ W)
          (ObjectProperty.homMk f : VA ⟶ W) :=
        IsPullback.of_map_of_faithful
          (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS F)) (IsPullback.of_hasPullback f U'.ι).flip
      have hi : IsOpenImmersion B S hS i.hom := isOpenImmersion_of_isPullback B S hS hsqA hU'.2
      have hdimV : dimension B S hS V hsq.isAlgebraicSpace ≤ (0 : ℕ) :=
        (dimension_le_of_isEtale B S hS hsq.isAlgebraicSpace W.2 f hsq.isEtale).trans hdim
      exact isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace B S hS i hi
        hV 0 1 hdimV (by omega) (by omega)
        (isQuasiCompactSpace_pullback B S hS B.contains_terminal f U'.ι hsq.isAlgebraicSpace W.2
          (IsAffineSpace.isQuasiCompactSpace hV) hU'qc hWqs) _ hN
    · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsInterHom B S hS hsq2) G hG 0 fun _ _ =>
        isZero_rightDerived_globalSectionsAb_of_isEmpty_points B S hS _
          ⟨fun x => hempty2.false (pointsMap B S hS _ (pullback.fst _ _) x)⟩ _ 0
  · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
      (isEtale_edsInterHom B S hS hsq1) F hF 0 fun _ _ =>
      isZero_rightDerived_globalSectionsAb_of_isEmpty_points B S hS _
        (isEmpty_points_pullback_of_disjoint B S hS U.ι U'.ι hdisj) _ 0

/-- **The induction of clause (1) of Stacks 0A4R.**  Let `X` be a quasi-compact
quasi-separated algebraic space with `dim X ≤ d` for a natural number `d`.  Then
`Hᑫ(X, F) = 0` for every quasi-coherent `𝒪_X`-module `F` and every `q > d`.

The proof is the induction principle of Stacks 08GP: on an affine object the higher cohomology
of a quasi-coherent module vanishes, and across an elementary distinguished square
`(U ⊆ W, V ⟶ W)` the Mayer–Vietoris sequence
(`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_succ_of_eds`) gives
`Hⁿ⁺¹(W, F) = 0` from `Hⁿ⁺¹(U, F) = Hⁿ⁺¹(V, F) = 0` and `Hⁿ(U ×_W V, F) = 0`.  The latter holds
by induction when `n > d`, and when `n = d ≥ 1` because `U ×_W V` is a quasi-compact open
subspace of the affine `V`, with `dim V ≤ dim X` since `V` is étale over `X`; this is
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace`.
When `n = d = 0` the step is
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_one_of_eds_of_dimension_le_zero`. -/
theorem isZero_rightDerived_globalSectionsAb_of_dimension_le (d : ℕ)
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hdim : dimension B S hS X.1 X.2 ≤ d) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (q : ℕ) (hq : d < q) :
    IsZero (((globalSectionsAb B S hS X).rightDerived q).obj F) := by
  refine qcqs_induction_on_self B S hS B.contains_terminal X hXqc hXqs
    (fun Y _ => ∀ (hY : IsAlgebraicSpace B S hS Y) (F : Modules.{u, u} B S hS Y hY),
      F.IsQuasicoherentOnSite → ∀ q : ℕ, d < q →
        IsZero (((globalSectionsAb B S hS ⟨Y, hY⟩).rightDerived q).obj F)) ?_ ?_ X.2 F hF q hq
  · intro V hVaff hY F hF q hq
    exact (isZero_rightDerived_globalSectionsAb_iff B S hS ⟨V.1.left.1, hY⟩ F q).2
      (isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace B S hS ⟨V.1.left.1, hY⟩
        hVaff F hF q (by omega))
  · intro W V U f _ hsq hWqc hWqs hUqc hVaff hPU hPV hPP hY F hF q hq
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    by_cases h0 : d = 0 ∧ n = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact isZero_rightDerived_globalSectionsAb_one_of_eds_of_dimension_le_zero B S hS
        (W := W.1.left) hsq hWqc hWqs
        ((dimension_le_of_isEtale B S hS W.1.left.2 X.2 W.1.hom.hom W.2).trans hdim) hUqc hVaff
        (fun G hG => hPU hsq.isOpenSubspace.1 G hG 1 (by omega)) F hF
    refine isZero_rightDerived_globalSectionsAb_succ_of_eds B S hS hsq F n ?_ ?_ ?_
    · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsOpenHom B S hS hsq) F hF (n + 1)
        fun G hG => hPU (edsOpen B S hS hsq).2 G hG (n + 1) (by omega)
    · exact isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsEtaleHom B S hS hsq) F hF (n + 1)
        fun G hG => hPV (edsEtale B S hS hsq).2 G hG (n + 1) (by omega)
    · refine isZero_restrictPush_of_forall_isQuasicoherentOnSite B S hS _
        (isEtale_edsInterHom B S hS hsq) F hF n fun G hG => ?_
      by_cases hn : d < n
      · exact hPP (edsInter B S hS hsq).2 G hG n hn
      rw [show n = d by omega]
      have hsnd : IsOpenImmersion B S hS (edsSnd B S hS hsq).hom :=
        isOpenImmersion_of_isPullback B S hS (isPullback_edsInter B S hS hsq)
          hsq.isOpenSubspace.2
      have hdimV : dimension B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ≤ d :=
        (dimension_le_of_isEtale B S hS V.1.left.2 X.2 V.1.hom.hom V.2).trans hdim
      have hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1 :=
        isQuasiCompactSpace_pullback B S hS B.contains_terminal _ _ (edsOpen B S hS hsq).2
          W.1.left.2 hUqc (IsAffineSpace.isQuasiCompactSpace hVaff) hWqs
      exact isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace B S hS
        (edsSnd B S hS hsq) hsnd hVaff d d hdimV le_rfl (by omega) hPqc G hG

end AlgebraicGeometry.Space
