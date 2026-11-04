module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay
public import StacksFrontier.RingTheory.Serre.Surjection
public import StacksFrontier.Algebra.Module.Reflexive

/-!
# Serre's condition `(Sₖ)` under further localization

If a finite module `T⁻¹M` satisfies `(Sₖ)` over `T⁻¹A`, then so does `T'⁻¹M` over `T'⁻¹A` for
every larger multiplicative set `T'`: the condition is local at the primes disjoint from the
multiplicative set. And `(Sₖ)` at a prime `𝔮` may be read on any localization `A → R'` at `𝔮`
and any localized module `M → M'` at `𝔮`.

## Main results

* `propertySkModule_localizedModule_of_le` — `(Sₖ)` passes to a larger multiplicative set.
* `propertySkModule_of_isLocalizedModule_atPrime` — `(Sₖ)` of `M_𝔮` over `A_𝔮` is `(Sₖ)` of any
  localization `M'` over any localization `R'` of `A` at `𝔮`.
-/

@[expose] public noncomputable section

open Dualizing

universe u

/-- **`(Sₖ)` passes to a larger multiplicative set.** If `T⁻¹M` satisfies `(Sₖ)` over `T⁻¹A`
and `T ≤ T'`, then `T'⁻¹M` satisfies `(Sₖ)` over `T'⁻¹A`. -/
theorem propertySkModule_localizedModule_of_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    {T T' : Submonoid A} (hTT' : T ≤ T') (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (k : ℕ)
    (h : PropertySkModule (Localization T) (LocalizedModule T M) k) :
    PropertySkModule (Localization T') (LocalizedModule T' M) k := by
  refine propertySkModule_localizedModule_of_forall T' M k fun q _ hq => ?_
  have hqT : Disjoint (T : Set A) (q : Set A) := hq.mono_left fun _ ha => hTT' ha
  let Q : Ideal (Localization T) := q.map (algebraMap A (Localization T))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint T _ q ‹_› hqT
  have hcomap : Q.comap (algebraMap A (Localization T)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint T _ ‹_› hqT
  obtain ⟨hd, hs⟩ := moduleDepth_and_moduleSupportDim_localizedModule_atPrime_localizedModule T M Q
  have hQ := h Q
  rw [hd, hs] at hQ
  have key : ∀ (p : Ideal A) [p.IsPrime], p = q →
      min (k : ℕ∞) ((moduleSupportDim (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)).unbotD 0) ≤
        moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M) →
      min (k : ℕ∞) ((moduleSupportDim (Localization.AtPrime q)
          (LocalizedModule.AtPrime q M)).unbotD 0) ≤
        moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q M) := by
    intro p _ hp
    subst hp
    exact id
  exact key _ hcomap hQ

/-- Transport a localization `M → M'` at `𝔮` along `A_𝔮 ≃ R'`: `M'` becomes an `A_𝔮`-module
isomorphic to `M_𝔮`, with `A_𝔮 → R'` surjective. -/
private theorem exists_atPrime_module_structure {A : Type u} [CommRing A] (q : Ideal A)
    [q.IsPrime] {R' : Type u} [CommRing R'] [Algebra A R'] [IsLocalization.AtPrime R' q]
    {M M' : Type u} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module R' M']
    [IsScalarTower A R' M'] (f : M →ₗ[A] M') [IsLocalizedModule q.primeCompl f] {P : Prop}
    (H : ∀ (_ : Algebra (Localization.AtPrime q) R') (_ : Module (Localization.AtPrime q) M')
      (_ : IsScalarTower (Localization.AtPrime q) R' M')
      (_ : LocalizedModule q.primeCompl M ≃ₗ[Localization.AtPrime q] M'),
      Function.Surjective (algebraMap (Localization.AtPrime q) R') →
      ringKrullDim R' = ringKrullDim (Localization.AtPrime q) → P) :
    P := by
  let e : Localization.AtPrime q ≃ₐ[A] R' := IsLocalization.algEquiv q.primeCompl _ _
  let : Algebra (Localization.AtPrime q) R' := e.toRingHom.toAlgebra
  let : Module (Localization.AtPrime q) M' := Module.compHom M' e.toRingHom
  have : IsScalarTower (Localization.AtPrime q) R' M' :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A (Localization.AtPrime q) M' := by
    refine ⟨fun a s m => ?_⟩
    change e (a • s) • m = a • (e s • m)
    rw [map_smul, smul_assoc]
  have : IsLocalizedModule q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl M) :=
    inferInstance
  exact H _ _ ‹_› ((IsLocalizedModule.iso q.primeCompl f).extendScalarsOfIsLocalization
    q.primeCompl (Localization.AtPrime q)) e.surjective
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm

/-- **`(Sₖ)` at a prime may be read on any localization.** Let `R'` be a localization of `A` at
the prime `𝔮` and `f : M → M'` a localization of the finite `A`-module `M` at `𝔮`, with `M'` an
`R'`-module. If `M_𝔮` satisfies `(Sₖ)` over `A_𝔮` then `M'` satisfies `(Sₖ)` over `R'`. -/
theorem propertySkModule_of_isLocalizedModule_atPrime {A : Type u} [CommRing A]
    [IsNoetherianRing A] (q : Ideal A) [q.IsPrime] {R' : Type u} [CommRing R'] [Algebra A R']
    [IsLocalization.AtPrime R' q] {M M' : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [AddCommGroup M'] [Module A M'] [Module R' M'] [IsScalarTower A R' M']
    [Module.Finite R' M'] (f : M →ₗ[A] M') [IsLocalizedModule q.primeCompl f] (k : ℕ)
    (h : PropertySkModule (Localization.AtPrime q) (LocalizedModule q.primeCompl M) k) :
    haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing q.primeCompl R' inferInstance
    PropertySkModule R' M' k := by
  have : IsNoetherianRing R' := IsLocalization.isNoetherianRing q.primeCompl R' inferInstance
  apply exists_atPrime_module_structure (R' := R') q f
  intro _ _ _ l' hsurj _
  have : Module.Finite (Localization.AtPrime q) M' := Module.Finite.equiv l'
  have hM' : PropertySkModule (Localization.AtPrime q) M' k :=
    propertySkModule_of_linearEquiv l'.symm k h
  exact propertySkModule_of_surjective_algebraMap (R := Localization.AtPrime q) (A := R')
    hsurj M' k hM'

/-- **Depth and dimension read on a localization at a prime.** For `R'` a localization of `A` at
`𝔮` and `f : M → M'` a localization of `M` at `𝔮`, the depth of `M'` over `R'` and the dimension
of `R'` are those of `M_𝔮` and `A_𝔮`. -/
theorem moduleDepth_and_ringKrullDim_of_isLocalizedModule_atPrime {A : Type u} [CommRing A]
    (q : Ideal A) [q.IsPrime] {R' : Type u} [CommRing R'] [Algebra A R']
    [IsLocalization.AtPrime R' q] {M M' : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [Module R' M'] [IsScalarTower A R' M']
    (f : M →ₗ[A] M') [IsLocalizedModule q.primeCompl f] :
    haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' q
    moduleDepth R' M' = moduleDepth (Localization.AtPrime q) (LocalizedModule q.primeCompl M) ∧
      ringKrullDim R' = ringKrullDim (Localization.AtPrime q) := by
  have : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' q
  apply exists_atPrime_module_structure (R' := R') q f
  intro _ _ _ l' hsurj hdim
  refine ⟨?_, hdim⟩
  rw [moduleDepth_eq_of_linearEquiv l']
  exact (moduleDepth_eq_of_surjective_algebraMap (S := Localization.AtPrime q) (T := R')
    hsurj M').symm

end
