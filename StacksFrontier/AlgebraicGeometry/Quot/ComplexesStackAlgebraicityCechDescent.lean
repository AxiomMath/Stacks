module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpaceProved

/-!
# Stacks 0DLN and 0DLM for `Complexes_{X/B}`, granted Stacks 0DLA and 0DIQ

In Situation 0DLE, `Complexes_{X/Y}` is an algebraic stack over `S` provided Čech descent
(Stacks 0DLA, `AlgebraicGeometry.Space.ComplexesSituation.CechDescent`) and derived existence
over towers `Spec R_n` (Stacks 0DIQ) hold. This is obtained from
`isAlgebraicStack_complexes_of_external_of_baseArtin_of_openVersality_changeOfBase` by
discharging its remaining inputs:

* Stacks 07W3 at schemes of the site,
  `AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`;
* Stacks 0DL7 for the base's `AlgebraicGeometry.Space.derivedPushoutEssentialImage`, through
  `AlgebraicGeometry.Space.exists_glue_of_isPushout_of_derivedPushoutEssentialImage`;
* the naturality statement `hnat` of Stacks 0DLL, by
  `fibreTrivialAutNatural_of_fibreLiftAutPullback` applied to `fibreLiftAutPullback`;
* the pullback statement `hpull` of Stacks 0DLL, by `fibreLiftClassPullback`.

## Main results

* `isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence`: Stacks 0DLN, granted
  Stacks 0DLA and 0DIQ.
* `isStronglyFormallyEffective_complexes_of_specLimitTower`: Stacks 0DLM, granted Stacks 0DIQ.

Stacks 0DLH, granted Stacks 0DLA, is `complexesFunctor_isStackInGroupoids_of_cechDescent`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLM](https://stacks.math.columbia.edu/tag/0DLM)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] complexesCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- In Situation 0DLE over `S` (`f : X ⟶ Y` proper, flat and of finite presentation),
`Complexes_{X/Y}` is an algebraic stack over `S`, given

* `h0DLA`: Čech descent for `Complexes` (Stacks 0DLA, Čech case);
* `h0DIQ`: existence of a pseudo-coherent limit of a compatible system of pseudo-coherent
  complexes over towers `Spec R_n` of `Spec Λ`, `Λ` of finite type over `ℤ` (Stacks 0DIQ). -/
theorem isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (h0DIQ : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B _ hΛ (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B _ hΛ (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B _ hΛ (D.space L.T)),
        (smallEtaleRingedSite B _ hΛ (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_external_of_baseArtin_of_openVersality_changeOfBase h0DLA h0DIQ
    (fun Λ _ _ hΛ => isPushout_of_isFlat_of_isPushout_schemeSpace B _ hΛ)
    (fun Λ _ _ hΛ => exists_glue_of_isPushout_of_derivedPushoutEssentialImage B _ hΛ
      (derivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B _ hΛ))
    (by
      intro _ _ D _ _ _ _ _ _ _ _ _ _ hK
      exact fibreTrivialAutNatural_of_fibreLiftAutPullback
        (complexesFunctor_isFiberedInGroupoids D) hK (fibreLiftAutPullback hK))
    (by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hK m hKm
      exact fibreLiftClassPullback hK m hKm)
    hS D

/-- In Situation 0DLE with `Y` final and `S` locally Noetherian, `Complexes_{X/S}` is strongly
formally effective, given `h0DIQ`: existence of a pseudo-coherent limit of a compatible system of
pseudo-coherent complexes over towers `Spec R_n` (Stacks 0DIQ). -/
theorem isStronglyFormallyEffective_complexes_of_specLimitTower {S : Scheme.{u}}
    {hS : B.Contains S} (D : ComplexesSituation B S hS)
    (h0DIQ : ∀ {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B S hS (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B S hS (D.space L.T)),
        (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y) :
    IsStronglyFormallyEffective B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  isStronglyFormallyEffective_complexes_of (D := D) h0DIQ (existsNegativeExtLocus_proved B S hS) hY

end AlgebraicGeometry.Space.ComplexesSituation

end
