module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor

/-!
# Derived completion of a single module agrees with its adic completion

Let `I` be an ideal of a Noetherian ring `A`. This file transports Stacks 0EEU from the
reflector produced by Stacks 0EET to the named derived completion endofunctor
`Stacks.Algebraization.adicCompletionFunctor`, so that the identification of derived `I`-adic
completion with ordinary `I`-adic completion is available for the functor the rest of the
library uses.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_tensor_flat` — the derived
  `I`-adic completion of `M ⊗[A] N` in degree zero, for `M` finite and `N` flat, is the ordinary
  `I`-adic completion of `M ⊗[A] N` in degree zero.
* `Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_localization` — the same for a
  localization of a finite module at one element.

## Implementation notes

Stacks 0EEU is stated for an arbitrary reflector onto the derived `I`-complete objects which is
additionally a derived limit of the tower of derived tensor products with `A/Iⁿ`. Stacks 0EET
supplies such a reflector for the canonical derived tensor product. Both of its clauses are then
moved to `adicCompletionFunctor` by the uniqueness of a left adjoint: the reflector of 0EET and
`Dualizing.derivedCompletion` are both left adjoint to the inclusion of the derived `I`-complete
objects, hence isomorphic, and the inclusion carries that isomorphism into `D(A)`.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
* [Stacks Project, Tag 0EET](https://stacks.math.columbia.edu/tag/0EET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AdicCompletionFlatTensor

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-- Transport an identification of derived with ordinary `I`-adic completion from an arbitrary
reflector onto the derived `I`-complete objects to `adicCompletionFunctor`. Both functors are
left adjoint to the inclusion of the derived `I`-complete objects, so they are isomorphic. -/
private theorem nonempty_iso_adicCompletionFunctor_of_reflector
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (Dualizing.derivedCompleteProperty A I).FullSubcategory)
    (adj : L ⊣ (Dualizing.derivedCompleteProperty A I).ι)
    (Q : Type u) [AddCommGroup Q] [Module A Q]
    (h : Nonempty ((L ⋙ (Dualizing.derivedCompleteProperty A I).ι).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A Q)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (AdicCompletion I Q)))) :
    Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A Q)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I Q))) :=
  h.map fun e => (Dualizing.derivedCompleteProperty A I).ι.mapIso
    (((adicCompletionAdjunction A I hI).leftAdjointUniq adj).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A Q))) ≪≫ e

/-- **Stacks 0EEU for the reflection model of derived completion.** Over a Noetherian ring,
the derived `I`-adic completion of the tensor product of a finite module with a flat module,
placed in degree zero, is its ordinary `I`-adic completion placed in degree zero. -/
theorem nonempty_iso_adicCompletionFunctor_single_tensor_flat
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Flat A N] :
    Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (TensorProduct A M N))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I (TensorProduct A M N)))) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adj⟩, hlim, -⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  exact nonempty_iso_adicCompletionFunctor_of_reflector A I hI L adj _
    ((derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
      A I T L ⟨adj⟩ hlim).1 M N)

/-- The same for a localization of a finite module at one element. -/
theorem nonempty_iso_adicCompletionFunctor_single_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M Mf : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup Mf] [Module A Mf] (g : A) (φ : M →ₗ[A] Mf)
    [IsLocalizedModule (Submonoid.powers g) φ] :
    Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A Mf)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I Mf))) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adj⟩, hlim, -⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  exact nonempty_iso_adicCompletionFunctor_of_reflector A I hI L adj _
    ((derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
      A I T L ⟨adj⟩ hlim).2 M Mf g φ)

end Stacks.Algebraization

end
