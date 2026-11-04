module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange

/-!
# The locus where `Rf_{T,*}𝓕_T` is locally free of given rank in one degree

Let `f : X ⟶ Y` be a flat, quasi-compact and quasi-separated morphism of algebraic spaces and
`𝓕` a quasi-coherent `𝒪_X`-module flat over `Y`. The formation of `K = Rf_*𝓕` commutes with
arbitrary base change (Stacks 08IR), so if `K` is perfect, then for `i, r ∈ ℤ` there is an open
subspace `V ⊆ Y` such that a morphism `T ⟶ Y` factors through `V` exactly when `Rf_{T,*}𝓕_T` is
a finite locally free module of rank `r` placed in degree `i`. This is the argument of the proof
of Stacks 0E6A, whose remaining input is the perfectness of `K` (Stacks 0CTM); the open subspace
comes from Stacks 0D20.

## Main results

* `AlgebraicGeometry.Space.torIndependent_of_isFlat_left`: a flat morphism is Tor independent
  of every morphism into its target.
* `AlgebraicGeometry.Space.exists_openSubspace_iff_of_nonempty_iso_derivedPullback`: Stacks 0D20
  for objects identified with the derived pullbacks of a perfect object.
* The reduction of Stacks 0E6A to perfectness of `Rf_*𝓕`, in the namespace
  `AlgebraicGeometry.Space`:
  `exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_derivedModulePushforward`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A flat morphism is Tor independent of every morphism into its target.** If
`f : X ⟶ Y` is flat, then `X` and `Y'` are Tor independent over `Y` (Stacks 08IP) for every
`g : Y' ⟶ Y`: the étale local rings of `X` are flat over those of `Y`. -/
theorem torIndependent_of_isFlat_left {X Y' Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hf : IsFlat B S hS f.hom) :
    TorIndependent X.2 Y'.2 Y.2 f.hom g.hom := by
  intro x y h
  refine ⟨etaleLocalRingMap X.2 f.hom x, etaleLocalRingMap Y'.2 g.hom y,
    etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x,
    etaleLocalRingMap_isEtaleLocalRingMap Y'.2 g.hom y, ?_⟩
  exact @RingTheory.TorIndependence.torIndependent_of_flat_left _ _ _ _ _ _
    (etaleLocalRingMap X.2 f.hom x).toAlgebra
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom y)).hom).toAlgebra
    ((isFlat_iff_forall_etaleLocalRingMap_flat B S hS f).1 hf x)

variable {Y : AlgebraicSpaces B S hS}

/-- **Stacks 0D20 for objects identified with derived pullbacks.** Let `E` be a perfect object of
`D(𝒪_Y)` and, for every morphism `g : T ⟶ Y`, let `K_g ∈ D(𝒪_T)` be isomorphic to `Lg^*E`.
For `i, r ∈ ℤ` there is an open subspace `V ⊆ Y` such that `g` factors through `V` exactly when
`K_g` is a finite locally free module of rank `r` placed in degree `i`. -/
theorem exists_openSubspace_iff_of_nonempty_iso_derivedPullback
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E) (i r : ℤ)
    (K : ∀ (T : AlgebraicSpaces B S hS) (_ : T ⟶ Y),
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS T)))
    (e : ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      Nonempty ((smallEtaleDerivedModulePullback B S hS g).obj E ≅ K T g)) :
    ∃ V : OpenSubspaces B S hS Y.1, ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      (∃ h : T ⟶ openSubspaceAsSpace B S hS V, h ≫ openSubspaceImmersion B S hS V = g) ↔
        IsFiniteLocallyFreeOfIntRankInDegree B S hS T (K T g) i r := by
  obtain ⟨U, -, hU, -⟩ := exists_isSingleDegreeRankLocus B S hS Y E i r hE
  refine ⟨U, fun T g => (hU T g).trans ⟨?_, ?_⟩⟩
  · rintro ⟨M, hM, ⟨φ⟩⟩
    exact ⟨M, hM, ⟨(e T g).some.symm ≪≫ φ⟩⟩
  · rintro ⟨M, hM, ⟨φ⟩⟩
    exact ⟨M, hM, ⟨(e T g).some ≪≫ φ⟩⟩

variable {X : AlgebraicSpaces B S hS}

/-- **Base change of `Rf_*𝓕` along `g : T ⟶ Y` for `f` flat and `𝓕` flat over `Y`.** For `f`
flat, quasi-compact and quasi-separated and `𝓕` quasi-coherent and flat over `Y`,
`Lg^*Rf_*𝓕 ≅ Rf_{T,*}𝓕_T`, with `𝓕_T` the (underived) pullback of `𝓕` to `X ×_Y T`: the base
change map is invertible by Stacks 08IR, and `L(g')^*𝓕 = (g')^*𝓕` by Stacks 0DKD (2). -/
theorem nonempty_derivedPullback_derivedModulePushforward_iso (f : X ⟶ Y)
    (hfl : IsFlat B S hS f.hom) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [hFq : F.IsQuasicoherentOnSite] (hF : IsFlatOver B S hS X.2 f.hom F)
    {T : AlgebraicSpaces B S hS} (g : T ⟶ Y) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj F)) ≅
      (derivedModulePushforward B S hS (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
          ((modulePullback B S hS (pullback.fst f g)).obj F))) := by
  have hbc : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g (pullback.snd f g)
      (pullback.fst f g) pullback.condition
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj F)) :=
    isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g _ _
    (IsPullback.of_hasPullback f g) hfqc hfqs (torIndependent_of_isFlat_left f g hfl) _
    (derivedCategoryB_singleFunctor_obj B S hS X.1 X.2 F hFq)
  have htor := isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver (pullback.fst f g)
    (pullback.snd f g) f g (IsPullback.of_hasPullback f g)
    (torIndependent_of_isFlat_left f g hfl) F hF
  refine ⟨asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g (pullback.snd f g)
      (pullback.fst f g) pullback.condition _) ≪≫
    (derivedModulePushforward B S hS (pullback.snd f g)).mapIso ?_⟩
  let C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)
  let K := (CochainComplex.singleFunctor C 0).obj F
  let P := (smallEtaleRingedToposHom B S hS (pullback.fst f g)).toModulesHom.pullbackModules
  exact (smallEtaleDerivedModulePullback B S hS (pullback.fst f g)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app F ≪≫
        ((DerivedCategory.quotientCompQhIso C).app K).symm) ≪≫
    @asIso _ _ _ _ ((smallEtaleDerivedModulePullbackComparison B S hS (pullback.fst f g)).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) htor ≪≫
    DerivedCategory.Qh.mapIso ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K).symm ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).app F ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso
          ((pullbackModulesIsoModulePullback B S hS (pullback.fst f g)).app F)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- **The reduction of Stacks 0E6A to perfectness of `Rf_*𝓕`.** Let `f : X ⟶ Y` be flat,
quasi-compact and quasi-separated and `𝓕` a quasi-coherent `𝒪_X`-module flat over `Y`. Suppose
`Rf_*𝓕` is perfect. Then for `i, r ∈ ℤ` there is an open subspace `V ⊆ Y` such that `g : T ⟶ Y`
factors through `V` exactly when `Rf_{T,*}𝓕_T` is a finite locally free module of rank `r`
placed in degree `i`. -/
theorem exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_derivedModulePushforward
    (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hF : IsFlatOver B S hS X.2 f.hom F) (i r : ℤ)
    (hperf : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj F))) :
    ∃ V : OpenSubspaces B S hS Y.1, ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      (∃ h : T ⟶ openSubspaceAsSpace B S hS V, h ≫ openSubspaceImmersion B S hS V = g) ↔
        IsFiniteLocallyFreeOfIntRankInDegree B S hS T
          ((derivedModulePushforward B S hS (pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
              ((modulePullback B S hS (pullback.fst f g)).obj F))) i r :=
  exists_openSubspace_iff_of_nonempty_iso_derivedPullback _ hperf i r _
    fun _ g => nonempty_derivedPullback_derivedModulePushforward_iso f hfl hfqc hfqs F hF g

end AlgebraicGeometry.Space

end
