module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleReflection
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFpqcDescentQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme
public import StacksFrontier.AlgebraicGeometry.Picard.ZariskiSiteFirstCohomology

/-!
# Invertibility of a quasi-coherent module descends along fpqc coverings of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module.
If `{f i : X i ⟶ X}` is an fpqc covering of `X` and every pullback `(f i)^*𝓕` is invertible,
then `𝓕` is invertible.  This is the step of the proof of Stacks 04WN which says that the module
obtained by descent (Stacks 04W8) from invertible modules is invertible.

The proof is the étale localization of the proof of Stacks 060X, with invertibility in place of
finite local freeness.  An invertible module on the small étale site of an algebraic space is the
same as a module finite locally free of rank one (Stacks 0B8M, 0B8Q), a rank is local on the site,
and the affine étale charts cover it, so it suffices to see that the restriction of `𝓕` to an
affine étale chart `T` has rank one.  That restriction has rank one as soon as the quasi-coherent
Zariski module `M` of the chart (Stacks 03DX (2)) is invertible.  The fpqc condition of Stacks
03MQ at the affine point `T ⟶ X` gives a finite affine fpqc covering of the scheme of `T` whose
members factor through the `X i`; the Zariski pullbacks of `M` to its members have invertible
associated modules, being read off from the pullbacks of the invertible `(f i)^*𝓕`, so they are
invertible by
`AlgebraicGeometry.SmallEtale.isInvertible_of_isFiniteLocallyFreeOfRank_one_associatedModule`,
and invertibility descends along fpqc coverings of schemes.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`: invertibility of a
  quasi-coherent module on an algebraic space descends along fpqc coverings.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Invertibility of a quasi-coherent module descends along fpqc coverings.**  Let `𝓕` be a
quasi-coherent `𝒪_X`-module on an algebraic space `X` and let `{f i : X i ⟶ X}` be an fpqc
covering such that every pullback `(f i)^*𝓕` is invertible.  Then `𝓕` is invertible. -/
theorem isInvertibleModule_of_pullback_isFpqcCovering
    {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (hinv : ∀ i, IsInvertibleModule (Xi i) ((modulePullback B S hS (f i)).obj F)) :
    IsInvertibleModule X F := by
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one F).2 ?_
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover
      (smallEtaleRingedSite B S hS X.obj X.property) F 1).2
    ⟨{T : SmallEtale B S hS X.obj // IsAffine (chartScheme T)}, fun T ↦ T.1,
      SmallEtale.coversTop_affineCharts B S hS X.obj, ?_⟩
  rintro ⟨A, hA⟩
  refine isFiniteLocallyFreeOfRank_over_of_isFiniteLocallyFreeOfRank_chartSchemeModule B S hS X
    F hF A 1 ?_
  have : SheafOfModules.IsQuasicoherent (chartSchemeModule B S hS X F hF A) :=
    isQuasicoherent_chartSchemeModule B S hS X F hF A
  have hMinv : Stacks.SheafOfModules.IsInvertible (chartScheme A).presheaf
      (chartScheme A).ringCatSheaf.2 (chartSchemeModule B S hS X F hF A) := by
    obtain ⟨E, _, hmem, hfactor⟩ :=
      hf.2 (⟨(SmallEtale.toOver B S hS X.obj).obj A, hA⟩ : BigAffineFppf B S hS) A.obj.hom
    have hmem' : (E.map (BigAffineFppf.toScheme B S hS)).presieve₀ ∈
        Scheme.fpqcPrecoverage (chartScheme A) := by
      rw [PreZeroHypercover.presieve₀_map]
      exact hmem
    refine Stacks.Picard.isInvertible_of_pullback_fpqcCover _ inferInstance
      { toPreZeroHypercover := E.map (BigAffineFppf.toScheme B S hS), mem₀ := hmem' } ?_
    intro j
    obtain ⟨i, a, ha⟩ := hfactor j
    let T' : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (E.X j)
    let g : T' ⟶ (SmallEtale.toOver B S hS X.obj).obj A :=
      (BigAffineFppf.inclusion B S hS).map (E.f j)
    change Stacks.SheafOfModules.IsInvertible _ _
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (chartSchemeModule B S hS X F hF A))
    set abar : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶
        Xi i := ObjectProperty.homMk a with habar
    have : SheafOfModules.IsQuasicoherent
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
          (chartSchemeModule B S hS X F hF A)) :=
      Stacks.SheafOfModules.schemePullback_isQuasicoherent _ _
    have hA' : IsInvertibleModule _
        ((modulePullback B S hS abar).obj ((modulePullback B S hS (f i)).obj F)) :=
      modulePullbackInvertible abar _ (hinv i)
    have hcomp : representedSpaceMap B S hS g ≫ chartToSpace B S hS X A = abar ≫ f i :=
      ObjectProperty.hom_ext _ ha.symm
    have hB : IsInvertibleModule _
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((modulePullback B S hS (chartToSpace B S hS X A)).obj F)) := by
      refine isInvertibleModule_of_iso
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS g)
          (chartToSpace B S hS X A)).app F).symm ?_
      rw [hcomp]
      exact isInvertibleModule_of_iso
        ((modulePullbackCompIso B S hS abar (f i)).app F) hA'
    let eF : (representedSmallEtaleModuleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.obj).obj A)).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            (chartScheme A) ((SmallEtale.toOver B S hS X.obj).obj A).left.property).obj
            (chartSchemeModule B S hS X F hF A)) ≅
        (modulePullback B S hS (chartToSpace B S hS X A)).obj F :=
      (representedSmallEtaleModuleEquivalence B S hS
            ((SmallEtale.toOver B S hS X.obj).obj A)).functor.mapIso
          (associatedModuleChartSchemeModuleIso B S hS X F hF A) ≪≫
        representedSmallEtaleChartSchemeEtaleModuleIso B S hS X F hF A ≪≫
        chartSmallEtaleRestrictionFunctorObjIso X F A ≪≫
        ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
          (isEtale_chartToSpace B S hS X A)).app F).symm
    have hC : IsInvertibleModule _ (representedSmallEtaleModule B S hS T'
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
            (chartSchemeModule B S hS X F hF A)))) :=
      isInvertibleModule_of_iso
        (representedAssociatedModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) (chartSchemeModule B S hS X F hF A))
        (isInvertibleModule_of_iso
          ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso eF).symm hB)
    exact
      AlgebraicGeometry.SmallEtale.isInvertible_of_isFiniteLocallyFreeOfRank_one_associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T') T'.left.property _
      ((isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B S hS T' _ 1).1
        ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one _).1 hC))
  have : Stacks.SheafOfModules.IsInvertible (chartScheme A).zariskiRingedSite.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (chartScheme A).zariskiRingedSite.O).property
      (chartSchemeModule B S hS X F hF A) := hMinv
  exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
    (chartScheme A).zariskiRingedSite _
    (Stacks.Picard.ZariskiSite.schemeRingedSite_isLocallyRinged (chartScheme A))

end AlgebraicGeometry.Space

end
