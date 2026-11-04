module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The projection-formula compatibility at the canonical models, and a witness for it

`Dualizing.ProjectionFormulaCompatibility` is the one obligation on which
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility` makes Stacks 0BZP
and both cases of Stacks 0BZM depend. It is stated at an *arbitrary* pair of models `Ff`, `Fi` of
derived extension of scalars along `R → A` and along `R' → A ⊗_R R'`, together with the two
morphisms exhibiting their universal properties.

* The obligation at the *canonical* models — the ones
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` chooses — is given a name,
  and the three statements of
  `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility` are restated at
  it, with the hypotheses of Stacks 0BZM and Stacks 0BZP plus the named obligation.
* The obligation holds at every object whose derived base change is zero, for every
  Tor-independent square and at every pair of models.

## Main definitions

* `Dualizing.ProjectionFormulaCompatibilityCanonical` — the obligation at the canonical models of
  derived extension of scalars.

## Main results

* `Dualizing.projectionFormulaCompatibility_of_isZero_baseChange` — the obligation holds whenever
  the derived base change of the object is zero, at every pair of models.
* `Dualizing.projectionFormulaCompatibility_of_isZero` — the same for a zero object, when derived
  base change along `R → R'` is additive.
* `Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_canonicalCompatibility`
  — **Stacks 0BZP**, conditional only on the canonical obligation.
* `Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_canonicalCompatibility` —
  the **flat case of Stacks 0BZM**, conditional only on the canonical obligation.
* `Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_canonicalCompatibility`
  — the **finite-Tor-dimension case of Stacks 0BZM**, conditional only on the canonical
  obligation.

## Implementation notes

The witness is proved from `CategoryTheory.Limits.IsZero.eq_of_tgt`: both sides of the obligation
are morphisms *into* the derived base change of the object, so they agree as soon as that object
is zero.

`Dualizing.ProjectionFormulaCompatibilityCanonical` applies
`Dualizing.ProjectionFormulaCompatibility` with its two `IsLeftDerivedFunctor` arguments passed
explicitly, as the fields of the chosen models, rather than left to instance synthesis: the
comparison morphisms, as structure fields, are typed with
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, which is only
definitionally equal to the composite the obligation expects.

Finite Tor dimension is read at the module universe the three rings force, exactly as in
`Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_projectionFormulaCompatibility`.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v uM

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

/-- The canonical model of unbounded derived extension of scalars along `R → A`, with the module
universe left free. -/
noncomputable def canonicalExtensionModel (R : Type uR) (A : Type uA) [CommRing R] [CommRing A]
    [Algebra R A] :
    TotalDerivedExtensionScalars.{uR, uM, uA, max uM uR uA + 1, max uM uR uA + 1}
      (algebraMap R A) :=
  totalDerivedExtensionScalars.{uR, uA, uM, _, _} (algebraMap R A)

/-- The canonical model of unbounded derived extension of scalars along `R' → A ⊗_R R'`, with the
module universe left free. -/
noncomputable def canonicalExtensionModelIncludeRight (R : Type uR) (A : Type uA)
    (R' : Type uRp) [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R'] :
    TotalDerivedExtensionScalars.{uRp, uM, max uA uRp, max uM uA uRp + 1, max uM uA uRp + 1}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom :=
  totalDerivedExtensionScalars.{uRp, max uA uRp, uM, _, _} _

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

section Witness

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

/-- **The projection-formula compatibility is inhabited.** It holds at every object of `D(R)`
whose derived base change along `R → R'` is a zero object — for every Tor-independent square and
at every pair of models of derived extension of scalars.

Both sides of `Dualizing.ProjectionFormulaCompatibility` are morphisms into
`baseChangeR.obj K`, so a zero target makes them equal. -/
theorem projectionFormulaCompatibility_of_isZero_baseChange
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : IsZero (baseChangeR.obj K)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  hz.eq_of_tgt _ _

/-- **The projection-formula compatibility holds at every zero object**, when derived base change
along `R → R'` is additive. -/
theorem projectionFormulaCompatibility_of_isZero [baseChangeR.Additive]
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (hz : IsZero K) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K :=
  projectionFormulaCompatibility_of_isZero_baseChange hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K (baseChangeR.map_isZero hz)

end Witness

section Canonical

/-- **The projection-formula compatibility at the canonical models.** The two models of derived
extension of scalars that `Dualizing.ProjectionFormulaCompatibility` takes as arguments — along
`R → A` and along `R' → A ⊗_R R'` — are the ones chosen by
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, each at the module universe
that the three rings of Stacks 0E2A force. -/
def ProjectionFormulaCompatibilityCanonical
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) : Prop :=
  @ProjectionFormulaCompatibility R A R' _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived K

/-- **The canonical obligation is inhabited**, at every object whose derived base change is zero.
This is `Dualizing.projectionFormulaCompatibility_of_isZero_baseChange` at the canonical
models. -/
theorem projectionFormulaCompatibilityCanonical_of_isZero_baseChange
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : IsZero (baseChangeR.obj K)) :
    ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K :=
  hz.eq_of_tgt _ _

/-- **Stacks 0BZP, conditional only on the canonical projection-formula compatibility.** This is
`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_projectionFormulaCompatibility` at the
canonical models. -/
theorem isIso_derivedHomBaseChange_app_of_isPerfect_of_canonicalCompatibility
    (hA : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  @isIso_derivedHomBaseChange_app_of_isPerfect_of_projectionFormulaCompatibility R A R'
    _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    _ _ (canonicalExtensionModel R A).isLeftDerived
    _ _ (canonicalExtensionModelIncludeRight R A R').isLeftDerived hA K hProj

/-- **The flat case of Stacks 0BZM, conditional only on the canonical projection-formula
compatibility.** This is
`Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_projectionFormulaCompatibility` at the
canonical models. -/
theorem isIso_derivedHomBaseChange_app_of_flat_of_canonicalCompatibility
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b)
    (hProj : ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  @isIso_derivedHomBaseChange_app_of_flat_of_projectionFormulaCompatibility R A R'
    _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    _ _ (canonicalExtensionModel R A).isLeftDerived
    _ _ (canonicalExtensionModelIncludeRight R A R').isLeftDerived
    hFlat hA K b hK hProj

/-- **The finite-Tor-dimension case of Stacks 0BZM, conditional only on the canonical
projection-formula compatibility.** The hypotheses on `A`, on `R'`, on the square and on `K` are
those of Stacks 0BZM, and the only other hypothesis is the single named obligation: `A` is
pseudo-coherent as an `R`-module, `R'` has finite Tor dimension over `R` read off a certified
derived tensor product as in Stacks 0652, the square is Tor-independent, and `K` is bounded
below.

This is
`Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_projectionFormulaCompatibility`
at the canonical models. Finite Tor dimension is read at the module universe the three rings
force. -/
theorem isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_canonicalCompatibility
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension D.tensor D.comparison
      D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{max v uR uA uRp} R)).plus K)
    (hProj : ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  @isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_projectionFormulaCompatibility R A R'
    _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    _ _ (canonicalExtensionModel R A).isLeftDerived
    _ _ (canonicalExtensionModelIncludeRight R A R').isLeftDerived
    D hFinite hA K hK hProj

end Canonical

end Dualizing

end
