module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartwiseBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect

/-!
# Cohomology and base change for the derived internal Hom

For a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated, `E`
perfect and a bounded above complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat over `Y`, the base
change map `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an isomorphism. If moreover
`f` is of finite presentation and `𝒢^•` is bounded, of finite presentation and with support proper
over `Y`, then `Rf_*R𝓗om(E, 𝒢^•)` is perfect.

## Main results

* `Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPerfect`: the base change isomorphism of
  Stacks 08JQ (1).
* `Space.isPerfect_derivedModulePushforward_derivedSheafHom_and_isIso_baseChange`:
  `Rf_*R𝓗om(E, 𝒢^•)` is perfect and its formation commutes with arbitrary base change.

## References

* [Stacks Project, Tag 0A1R](https://stacks.math.columbia.edu/tag/0A1R)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKH](https://stacks.math.columbia.edu/tag/0DKH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- For a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated, `E`
perfect and a bounded above complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat over `Y`, the base
change map `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`
(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap`) is an isomorphism: the case of a
perfect `E` of Stacks 08JQ (1). -/
theorem isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPerfect
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G) := by
  obtain ⟨b, hb⟩ := hGb
  have : G.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff G b).2 hb
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) g'
  have hK := qcohDerived_Q_obj_of_isQuasicoherentOnSite G hq
  have hK' := qcohDerived_Q_obj_of_isQuasicoherentOnSite
    (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)
    fun n => isQuasicoherentOnSite_pullbackModules B S hS g' (G.X n) (hq n)
  have h2 := affineChartwiseBaseChange_sheafHom_of_isPerfect f g f' g' sq.w E hE _ hK _ hK' _
    (affineChartwiseBaseChange_pullbackQComparison B S hS sq G b hq hfl)
  have hiso := isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange B S hS sq hfqc
    hfqs _ (qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X _ _ hE hK) _
    (qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X' _ _
      (isPerfect_smallEtaleDerivedModulePullback g' E hE) hK') _ h2
  unfold smallEtaleDerivedSheafHomBaseChangeMap smallEtaleDerivedModulePullbackQComparison
  rw [Functor.map_comp, ← Category.assoc]
  exact isIso_smallEtaleDerivedBaseChangeComp_of_comp_inv B S hS f g f' g' sq.w _ _ _ hiso
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _)))

/-- For `f : X ⟶ Y` of finite presentation, a perfect `E` and a bounded complex `𝒢^•` of
`𝒪_X`-modules of finite presentation, flat over `Y`, with support proper over `Y`,
`Rf_*R𝓗om(E, 𝒢^•)` is perfect, and its formation commutes with arbitrary base change: for every
cartesian square, `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an isomorphism. -/
@[stacks 0A1R]
theorem isPerfect_derivedModulePushforward_derivedSheafHom_and_isIso_baseChange
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
        ((derivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G) := by
  refine ⟨isPerfect_derivedModulePushforward_derivedSheafHom_of_perfectness f E hE G
    (isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f hf _
      (isPerfect_smallEtaleDerivedDual B S hS X E hE) G hGb hGfp hGflat hGsupp).1,
    fun g f' g' sq => ?_⟩
  obtain ⟨b, hb⟩ := hGb.bddAbove
  exact isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPerfect sq hf.2.1 hf.2.2 E hE G
    ⟨b, fun i hi => of_not_not fun h => not_le.2 hi (hb h)⟩
    (fun n => @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ (G.X n)
      (isFinitePresentationOnSite_of_isFinitePresentation' (G.X n) (hGfp n))) hGflat

end AlgebraicGeometry.Space

end
