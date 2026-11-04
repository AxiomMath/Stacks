module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# Base change for derived Hom: reduction to the base ring

Let `R → A` and `R → R'` be Tor-independent ring maps, `A' = A ⊗_R R'`. Stacks 0BZM asserts that
the base-change morphism
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')`
of `Dualizing.derivedHomBaseChange` is invertible for `K ∈ D⁺(R)` when `A` is pseudo-coherent over
`R` and `R'` has finite Tor dimension over `R`. Stacks 0E2A reduces this to a statement about
derived Hom over `R'` alone, and the first step of that reduction is that it suffices to check
invertibility after restricting scalars along `R' → A'`: restriction of scalars is exact and
reflects isomorphisms, so the functor it induces on derived categories is conservative.

This file records that reduction at the exact shape in which Stacks 0BZM needs it.

## Main results

* `Dualizing.isIso_derivedHomBaseChange_app_of_restrictScalars` — the base-change morphism at an
  object of `D(R)` is invertible as soon as its restriction to `D(R')` is.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extension of scalars along a ring map is an additive functor. -/
local instance {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T) :
    (ModuleCat.extendScalars.{uS, uT, w} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

/-- Invertibility of the derived-Hom base-change morphism may be checked after restricting
scalars along `R' → A ⊗_R R'`, because that restriction induces a conservative functor on derived
categories. This is the opening move of the proof of Stacks 0E2A, and hence of Stacks 0BZM. -/
theorem isIso_derivedHomBaseChange_app_of_restrictScalars
    {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
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
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (h : IsIso ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
      ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K))) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  have := h
  isIso_of_reflects_iso _ (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory

end Dualizing

end
