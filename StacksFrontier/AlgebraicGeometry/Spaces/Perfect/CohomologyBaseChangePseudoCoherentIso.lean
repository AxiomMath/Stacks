module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent

/-!
# Pseudo-coherence and base change of `Rf_*(E ⊗^L 𝒢^•)`: Stacks 0CTL and 0CTN

For `f : X ⟶ Y` of finite presentation, `E` pseudo-coherent and `𝒢^•` a bounded above complex of
`𝒪_X`-modules of finite presentation, flat over `Y`, with support proper over `Y`,
`Rf_*(E ⊗^L 𝒢^•)` is pseudo-coherent and its formation commutes with arbitrary base change
(Stacks 0CTL). For `f` flat and proper of finite presentation, `Rf_*E` is pseudo-coherent and its
formation commutes with arbitrary base change (Stacks 0CTN).

## Main results

* `isPseudoCoherent_derivedModulePushforward_derivedTensor_and_isIso_baseChange`:
  `Rf_*(E ⊗^L 𝒢^•)` is pseudo-coherent and commutes with arbitrary base change (Stacks 0CTL).
* `isPseudoCoherent_derivedModulePushforward_and_isIso_baseChange`: for `f` flat and proper of
  finite presentation, `Rf_*E` is pseudo-coherent and commutes with base change (Stacks 0CTN).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0CTL.** For `f : X ⟶ Y` of finite presentation, a pseudo-coherent `E` and a bounded
above complex `𝒢^•` of `𝒪_X`-modules of finite presentation, flat over `Y`, with support proper
over `Y`, `Rf_*(E ⊗^L 𝒢^•)` is pseudo-coherent, and its formation commutes with arbitrary base
change: for every cartesian square,
`Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` is an isomorphism. -/
@[stacks 0CTL]
theorem isPseudoCoherent_derivedModulePushforward_derivedTensor_and_isIso_baseChange
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
        ((derivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
          (((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj
            (DerivedCategory.Q.obj (((modulePullback B S hS g').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))
          ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, DerivedCategory.Q.obj G) ≫
            ((smallEtaleDerivedTensor B S hS X').obj
              ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
              (smallEtaleDerivedModulePullbackQComparison g' G))) :=
  ⟨isPseudoCoherent_derivedModulePushforward_derivedTensor_of_perfectness
      (fun f' hf' E' hE' G' h₁ h₂ h₃ h₄ =>
        (isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f' hf' E' hE' G'
          h₁ h₂ h₃ h₄).1) f hf E hE G hGb hGfp hGflat hGsupp,
    fun _ _ _ sq => isIso_smallEtaleDerivedBaseChangeComp_derivedTensor sq hf.2.1 hf.2.2 E
      (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE) G hGb
      (fun n => @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ (G.X n)
        (isFinitePresentationOnSite_of_isFinitePresentation' (G.X n) (hGfp n))) hGflat⟩

/-- **Stacks 0CTN.** For a flat and proper morphism `f : X ⟶ Y` of finite presentation and a
pseudo-coherent `E`, `Rf_*E` is pseudo-coherent, and its formation commutes with arbitrary base
change: for every cartesian square, the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of
Stacks 07A7 is an isomorphism. -/
@[stacks 0CTN]
theorem isPseudoCoherent_derivedModulePushforward_and_isIso_baseChange
    (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom) (hpr : IsProper B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
        ((derivedModulePushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) :=
  isPseudoCoherent_derivedModulePushforward_of_perfectness
    (fun f' hf' E' hE' G' h₁ h₂ h₃ h₄ =>
      (isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f' hf' E' hE' G'
        h₁ h₂ h₃ h₄).1) f hfl hpr hf E hE

end AlgebraicGeometry.Space

end
