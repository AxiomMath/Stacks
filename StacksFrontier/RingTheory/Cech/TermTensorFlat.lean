module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.Homology.DerivedComplete.AdicCompletionFunctorSingleIso
public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# The Čech terms are tensor products with flat modules

Let `A` be a commutative ring, let `g : Fin r → A` be a finite family of elements and let `M` be
an `A`-module. The degree-`p` term of the extended alternating Čech complex of `M` is the direct
sum `⨁_{#s = p} M_{∏ i ∈ s, g i}` of localizations of `M`. Each localization is the tensor product
of `M` with the corresponding localization of `A`, and a direct sum of localizations of `A` is a
flat `A`-module, so the whole term is `M ⊗[A] N` for a single flat module `N`.

## Main results

* `Stacks.LocalCohomology.nonempty_linearEquiv_cechTerm_tensor_flat`: the degree-`p` Čech term
  of `M` is linearly equivalent to `M ⊗[A] N` for some flat `A`-module `N`.
* `Stacks.LocalCohomology.nonempty_iso_adicCompletionFunctor_single_cechTerm`: over a Noetherian
  ring the derived `I`-adic completion of the degree-`p` Čech term of a finite module, placed in
  degree zero, is its ordinary `I`-adic completion in degree zero.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.LocalCohomology

/-- The tensor product of `M` with the localization of the base ring at `S` is linearly
equivalent to the localization of `M` at `S`. -/
private def linearEquivTensorLocalization {A : Type u} [CommRing A] (S : Submonoid A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    TensorProduct A M (Localization S) ≃ₗ[A] LocalizedModule S M :=
  (TensorProduct.comm A M (Localization S)).trans
    (IsLocalizedModule.linearEquiv S (TensorProduct.mk A (Localization S) M 1)
      (LocalizedModule.mkLinearMap S M))

/-- The degree-`p` term of the extended alternating Čech complex of `M` is the tensor product
of `M` with a flat module: the direct sum of the localizations `A_{g_S}`. -/
theorem nonempty_linearEquiv_cechTerm_tensor_flat {A : Type u} [CommRing A] {r : ℕ}
    (g : Fin r → A) (M : Type u) [AddCommGroup M] [Module A M] (p : ℕ) :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Flat A N),
      Nonempty (TensorProduct A M N ≃ₗ[A] Cech.cechTerm g M p) := by
  refine ⟨DirectSum {s : Finset (Fin r) // s.card = p}
      fun s => Localization (Cech.cechSub g s.1), inferInstance, inferInstance, inferInstance,
    ⟨(TensorProduct.directSumRight A A M fun s : {s : Finset (Fin r) // s.card = p} =>
        Localization (Cech.cechSub g s.1)).trans
      (DirectSum.congrLinearEquiv fun s => linearEquivTensorLocalization (Cech.cechSub g s.1) M)⟩⟩

/-- Over a Noetherian ring, derived `I`-adic completion of the degree-`p` term of the Čech complex
of a finite module, placed in degree zero, is its ordinary `I`-adic completion placed in degree
zero. -/
theorem nonempty_iso_adicCompletionFunctor_single_cechTerm {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) {r : ℕ} (g : Fin r → A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (p : ℕ) :
    Nonempty ((Stacks.Algebraization.adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Cech.cechTerm g M p))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I (Cech.cechTerm g M p)))) := by
  obtain ⟨N, instGroup, instModule, instFlat, ⟨e⟩⟩ :=
    nonempty_linearEquiv_cechTerm_tensor_flat g M p
  let := instGroup
  let := instModule
  let := instFlat
  obtain ⟨h⟩ :=
    Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_tensor_flat A I hI M N
  exact ⟨(Stacks.Algebraization.adicCompletionFunctor A I hI).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e.symm.toModuleIso) ≪≫ h ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      ((AdicCompletion.congr I e).restrictScalars A).toModuleIso⟩

end Stacks.LocalCohomology

end
