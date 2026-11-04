module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Free

/-!
# A finite module over a reduced Noetherian ring is free over a nonzero localization

Let `A` be a nonzero reduced Noetherian ring and `M` a finite `A`-module.  At a minimal prime
`𝔭` of `A` the local ring `A_𝔭` is a reduced local ring of dimension zero, hence a field, so
`M_𝔭` is free; and a finitely presented module free at a prime is free over a principal
localization at an element outside that prime.  So there is a **nonzero** `f ∈ A` with `M_f`
free over `A_f`.

Freeness of a localization does not depend on the model of the localization: if `M ⟶ M'` is a
localization of modules at `S` and `M'` is a module over some localization `R_S` of `R`, then
`M'` is free over `R_S` as soon as `LocalizedModule S M` is free over `Localization S`.

## Main results

* `Module.Free.of_isLocalizedModule_of_free_localizedModule`: freeness of a localization of modules
transfers between
  models.
* `Module.exists_ne_zero_free_localizedModule_away_of_isReduced`: a finite module over a nonzero
  reduced Noetherian ring is free over a principal localization at a nonzero element.
-/

@[expose] public section

open Module TensorProduct

/-- **Freeness of a localization of modules does not depend on the model.**  If `f : M ⟶ M'` is
a localization at `S`, `M'` is a module over a localization `Rₛ` of `R` at `S`, and
`LocalizedModule S M` is free over `Localization S`, then `M'` is free over `Rₛ`.

Both are base changes of `M`, the first along `R ⟶ Localization S` and the second along
`R ⟶ Rₛ`, and the two localizations of `R` are isomorphic `R`-algebras. -/
theorem Module.Free.of_isLocalizedModule_of_free_localizedModule {R : Type*} [CommRing R]
    (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ] {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module Rₛ M']
    [IsScalarTower R Rₛ M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ M' := by
  let e : Localization S ≃ₐ[R] Rₛ := IsLocalization.algEquiv S _ _
  let : Algebra (Localization S) Rₛ := e.toRingHom.toAlgebra
  have : IsScalarTower R (Localization S) Rₛ :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  have : Module.Free (Localization S) (Localization S ⊗[R] M) := .of_equiv
    (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)).equiv.symm
  exact .of_equiv ((AlgebraTensorModule.cancelBaseChange R (Localization S) Rₛ Rₛ M).trans
    (IsLocalizedModule.isBaseChange S Rₛ f).equiv)

/-- **A finite module over a nonzero reduced Noetherian ring is free over a principal
localization at a nonzero element.**

The localization of `A` at a minimal prime `𝔭` is a reduced local ring of dimension zero, hence
a field, over which `M_𝔭` is free; a finitely presented module free at `𝔭` is free over `A_f`
for some `f ∉ 𝔭`, and such an `f` is not nilpotent, hence nonzero in the reduced ring `A`. -/
theorem Module.exists_ne_zero_free_localizedModule_away_of_isReduced (A : Type*) [CommRing A]
    [IsReduced A] [IsNoetherianRing A] [Nontrivial A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := m) bot_le
  have hpp : p.IsPrime := hp.1.1
  have : Subsingleton (PrimeSpectrum (Localization.AtPrime p)) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp _
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := inferInstance
  have hfield : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  let := hfield.toField
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨f, fun h0 => hf (h0 ▸ p.zero_mem), hfree⟩

end
