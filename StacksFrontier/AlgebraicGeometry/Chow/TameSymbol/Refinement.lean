module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined

/-!
# Stacks 0EAT with no refinement on the right-hand side

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring, let `A ⊆ B` be a finite ring extension
with `𝔪` not an associated prime of `B`, and let `a, b ∈ A` be nonzerodivisors. Stacks 0EAT
asserts

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product being over the maximal ideals of `B`.

`Stacks.Chow.normProd_eq_prod_norm_normProd` proves that equation with *both* sides read relative
to a common refinement `B ⊆ C`: the factor at `𝔮` there is the norm pushforward of a family of
symbols on the local rings of `C` to `B_𝔮`, not a tame symbol on `B_𝔮`. This file removes the
refinement from the right-hand side.

What makes that possible is the second half of Stacks 0EAR, the independence of the formula
Stacks 0EAQ from the auxiliary extension, which the source reduces to

`λ ^ length_{B_𝔮}(B_𝔮/πB_𝔮) = ∏_𝔯 Norm_{κ(𝔯)/κ(𝔮)}(λ) ^ length_{C_𝔯}(C_𝔯/πC_𝔯)`

for `λ` a unit of `κ(𝔮)` — the norm of an element of the base field is its degree-th power, and
`length_{B_𝔮}(B_𝔮/πB_𝔮) = ∑_𝔯 [κ(𝔯) : κ(𝔮)] length_{C_𝔯}(C_𝔯/πC_𝔯)`. That identity is
`Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow_fibre`. Applied to the unit part of a local
factorization it says that the local factor of Stacks 0EAQ at `𝔮` is recovered from the factors
at the maximal ideals of `C` over `𝔮`: `Stacks.Chow.prod_norm_factorizationValue_algebraMap`.

Summing that over the maximal ideals of `B`, with the fibred decomposition of the maximal ideals
of `C` (`Stacks.Localization.prod_maximalSpectrum_eq_prod_prod`) and transitivity of norms for
`κ(𝔯)/κ(𝔮)/κ(𝔪)` (Stacks 0BIJ), gives Stacks 0EAT in the form

`∏_𝔯 Norm_{κ(𝔯)/κ(𝔪)}(∂_{C_𝔯}(a, b)) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

where the `∂_{C_𝔯}` and the `∂_{B_𝔮}` are *arbitrary* tame symbols in the sense of Stacks 0EAH on
the local rings of `C` and of `B`. Both sides are intrinsic: no choice of refinement enters the
right-hand side, and the left-hand side is the recipe of Stacks 0EAQ computed over `C`. The hinge
is that a tame symbol on a local ring is pinned down on a pair admitting a simultaneous power
factorization (`Stacks.Chow.RegularTameSymbol.apply_eq_factorizationValue`), and a tame-symbol
preparation of `a, b` over `B` supplies such a factorization at every maximal ideal of `B` and,
after pushing it forward, at every maximal ideal of `C`.

As a corollary the recipe of Stacks 0EAQ computed over the refinement `C` agrees with the recipe
computed over `B`, which is Stacks 0EAR for the choice of the auxiliary extension along a tower:
`AlgebraicGeometry.TameSymbolPreparation.preparationSymbolValue_eq_normProd_refinement`.

## Main results

* `Stacks.Chow.factorizationValue_algebraMap` — the local factor of Stacks 0EAQ at the image of a
  factorization is the image of the unit part, raised to the order of vanishing downstairs.
* `Stacks.Chow.mem_nonZeroDivisors_algebraMap_fibre` — a nonzerodivisor of `B_𝔮` stays a
  nonzerodivisor in the local ring of `C` at a maximal ideal over `𝔮`.
* `Stacks.Chow.prod_norm_factorizationValue_algebraMap` — Stacks 0EAR for the auxiliary
  extension, at one maximal ideal of `B`.
* `Stacks.Chow.normProd_eq_prod_norm_tameSymbol` — **Stacks 0EAT with no refinement on the
  right-hand side.**
* `AlgebraicGeometry.TameSymbolPreparation.preparationSymbolValue_eq_normProd_refinement` —
  Stacks 0EAR for the choice of the auxiliary extension, along a tower.

## References

* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0BIJ](https://stacks.math.columbia.edu/tag/0BIJ)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

universe u v w

namespace Stacks.Chow

/-! ### The local factor of Stacks 0EAQ along a local homomorphism -/

section ImageOfFactorization

variable {R : Type*} [CommRing R] [IsLocalRing R] {S : Type*} [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- The residue of the image of a unit is the image of its residue. -/
theorem units_map_residue_algebraMap (u : Rˣ) :
    Units.map (residue S).toMonoidHom (Units.map (algebraMap R S).toMonoidHom u) =
      Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom
        (Units.map (residue R).toMonoidHom u) :=
  Units.ext (by simp)

/-- **The local factor of Stacks 0EAQ at the image of a factorization.** Pushing a simultaneous
power factorization along a local homomorphism `R → S` replaces the unit part of the factor by
its image in `κ(S)` and the exponent by the order of vanishing of the image of the parameter. -/
theorem factorizationValue_algebraMap (p : R) (u v : Rˣ) (e f : ℕ) :
    factorizationValue (algebraMap R S p) (Units.map (algebraMap R S).toMonoidHom u)
        (Units.map (algebraMap R S).toMonoidHom v) e f =
      Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom
          ((-1) ^ (e * f) * Units.map (residue R).toMonoidHom u ^ f *
            (Units.map (residue R).toMonoidHom v)⁻¹ ^ e) ^
        (Ring.ord S (algebraMap R S p)).toNat := by
  have hneg : Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom
      (-1 : (ResidueField R)ˣ) = (-1 : (ResidueField S)ˣ) := Units.ext (by simp)
  simp only [factorizationValue, map_mul, map_pow, map_inv, hneg, units_map_residue_algebraMap]

end ImageOfFactorization

/-! ### Stacks 0EAR for the auxiliary extension, at one maximal ideal -/

section Fibre

variable {B : Type v} [CommRing B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
  {C : Type w} [CommRing C] [Algebra B C] [Module.Finite B C] [Algebra.IsIntegral B C]
  (q : MaximalSpectrum B)
  [Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
  [∀ w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
    Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (w.asIdeal.under C))]
  [∀ w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
    Localization.AtPrime.IsLiesOverAlgebra q.asIdeal (w.asIdeal.under C)]

omit [Module.Finite B C]
  [Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))] in
/-- **A nonzerodivisor of `B_𝔮` stays a nonzerodivisor in the local ring of `C` at a maximal
ideal over `𝔮`.** It stays one in the semilocalization `C_𝔮` because `𝔪_𝔮` is not an associated
prime of it, hence in the localization of `C_𝔮` at a maximal ideal, which is the local ring of
`C` at the prime below. -/
theorem mem_nonZeroDivisors_algebraMap_fibre
    (hass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    {p : Localization.AtPrime q.asIdeal}
    (hp : p ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal)) :
    algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime (w.asIdeal.under C)) p ∈
      nonZeroDivisors (Localization.AtPrime (w.asIdeal.under C)) := by
  let := krullDimLE_one_localizationAtPrime q.asIdeal
  have h1 : algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) p ∈
      nonZeroDivisors (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) :=
    mem_nonZeroDivisors_algebraMap hass hp
  have h2 : algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime w.asIdeal) p ∈
      nonZeroDivisors (Localization.AtPrime w.asIdeal) := by
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
      (Localization.AtPrime w.asIdeal)]
    exact IsLocalization.nonZeroDivisors_le_comap (M := w.asIdeal.primeCompl)
      (S := Localization.AtPrime w.asIdeal) h1
  have h3 := mem_nonZeroDivisors_ringEquiv (fibreLocalizationAlgEquiv q w).symm.toRingEquiv h2
  rwa [show (fibreLocalizationAlgEquiv q w).symm.toRingEquiv
        (algebraMap (Localization.AtPrime q.asIdeal) (Localization.AtPrime w.asIdeal) p) =
      algebraMap (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (w.asIdeal.under C)) p from
    (fibreLocalizationAlgEquiv q w).symm_apply_eq.mpr
      (fibreLocalizationAlgEquiv_algebraMap q w p).symm] at h3

/-- **Stacks 0EAR for the auxiliary extension, at one maximal ideal of `B`.** The local factor of
the formula Stacks 0EAQ at `𝔮` is recovered from the factors of the pushed-forward factorization
at the maximal ideals of `C` over `𝔮`: taking the residue-field norms down to `κ(𝔮)` and
multiplying gives back the factor at `𝔮`.

This is the identity the source's comparison of two auxiliary extensions reduces to, by
`Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow_fibre`: the norm of an element of `κ(𝔮)` is its
`[κ(𝔯) : κ(𝔮)]`-th power and
`length_{B_𝔮}(B_𝔮/πB_𝔮) = ∑_𝔯 [κ(𝔯) : κ(𝔮)] length_{C_𝔯}(C_𝔯/πC_𝔯)`. -/
theorem prod_norm_factorizationValue_algebraMap
    (hass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hinj : Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquot : ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
      (⊤ : Submodule (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
      LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    {p : Localization.AtPrime q.asIdeal}
    (hp : p ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (u₁ u₂ : (Localization.AtPrime q.asIdeal)ˣ) (e f : ℕ) :
    ∏ w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
        Units.map (Algebra.norm (ResidueField (Localization.AtPrime q.asIdeal)) :
            ResidueField (Localization.AtPrime (w.asIdeal.under C)) →*
              ResidueField (Localization.AtPrime q.asIdeal))
          (factorizationValue
            (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (w.asIdeal.under C)) p)
            (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (w.asIdeal.under C))).toMonoidHom u₁)
            (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (w.asIdeal.under C))).toMonoidHom u₂) e f) =
      factorizationValue p u₁ u₂ e f := by
  have hfv : factorizationValue p u₁ u₂ e f =
      ((-1) ^ (e * f) *
          Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom u₁ ^ f *
          (Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom u₂)⁻¹ ^ e) ^
        (Ring.ord (Localization.AtPrime q.asIdeal) p).toNat := rfl
  rw [hfv, pow_ord_toNat_eq_prod_norm_pow_fibre q hass hinj hquot _ hp]
  exact Finset.prod_congr rfl fun w _ =>
    congrArg _ (factorizationValue_algebraMap p u₁ u₂ e f)

end Fibre

/-! ### Stacks 0EAT with no refinement on the right-hand side -/

/-- The local parameter of a tame-symbol preparation at a maximal ideal is a nonzerodivisor. -/
private theorem parameter_mem_nonZeroDivisors {A : Type u} [CommRing A] [IsLocalRing A]
    {B : Type v} [CommRing B] [Algebra A B] {n : ℕ} {a : Fin n → A}
    (P : TameSymbolPreparation a B) (q : MaximalSpectrum B) :
    P.parameter q.asIdeal ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal) :=
  isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal)

section Tower

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [Algebra A B]
  {C : Type w} [CommRing C] [Algebra B C] [Module.Finite B C] [Algebra.IsIntegral B C]
  [Algebra A C] [IsScalarTower A B C]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsNoetherianRing (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, Ring.KrullDimLE 1 (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ q : MaximalSpectrum B,
    Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
  [∀ (q : MaximalSpectrum B)
      (w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (w.asIdeal.under C))]
  [∀ (q : MaximalSpectrum B)
      (w : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
    Localization.AtPrime.IsLiesOverAlgebra q.asIdeal (w.asIdeal.under C)]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsNoetherianRing (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, Ring.KrullDimLE 1 (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ q : MaximalSpectrum B, Fintype
    (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))] in
/-- **A tame-symbol preparation over `B` factorizes the family in the local rings of `C`.** At a
maximal ideal of the semilocalization `C_𝔮` the factorization `a k = u_{k, 𝔮} π_𝔮^{e_{k, 𝔮}}`
of the preparation is pushed forward along `B_𝔮 → C_𝔯`, where it is again a factorization of
`a k` into a unit times a power of one element. -/
theorem algebraMap_eq_factorUnit_mul_parameter_pow_fibre (q : MaximalSpectrum B)
    (u : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (k : Fin n) :
    algebraMap A (Localization.AtPrime (u.asIdeal.under C)) (a k) =
      (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom
          (P.factorUnit q.asIdeal k) : Localization.AtPrime (u.asIdeal.under C)) *
        algebraMap (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime (u.asIdeal.under C)) (P.parameter q.asIdeal) ^
          P.exponent q.asIdeal k := by
  have htower := isScalarTower_localizationAtPrime_under (A := A) q u
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (u.asIdeal.under C)),
    IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal),
    P.factorization q.asIdeal k, map_mul, map_pow]
  rfl

omit [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ q : MaximalSpectrum B, Fintype
    (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))] in
/-- **The factor of the formula Stacks 0EAQ at a maximal ideal of `C` over `𝔮`.** A tame-symbol
preparation of the family `a` over `B` writes `a k` at `𝔮` as a unit times a power of the local
parameter; pushing that factorization into the local ring of `C` at a maximal ideal over `𝔮`
factorizes `a k` there as well, so every tame symbol on that local ring takes the value of the
formula Stacks 0EAQ on the pushed-forward data. -/
theorem tameSymbol_fibre_eq_factorizationValue
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (symbC : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (q : MaximalSpectrum B)
    (hfass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (u : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    symbC (fibrePoint q u) (toExtensionNonZeroDivisor hC (fibrePoint q u) x)
        (toExtensionNonZeroDivisor hC (fibrePoint q u) y) =
      factorizationValue
        (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (u.asIdeal.under C)) (P.parameter q.asIdeal))
        (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom (P.factorUnit q.asIdeal i))
        (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom (P.factorUnit q.asIdeal j))
        (P.exponent q.asIdeal i) (P.exponent q.asIdeal j) := by
  exact (symbC (fibrePoint q u)).apply_eq_factorizationValue
    ⟨_, mem_nonZeroDivisors_algebraMap_fibre q hfass u (parameter_mem_nonZeroDivisors P q)⟩
    _ _ _ _ _ _
    (by rw [toExtensionNonZeroDivisor_val, hx]
        exact algebraMap_eq_factorUnit_mul_parameter_pow_fibre q u P i)
    (by rw [toExtensionNonZeroDivisor_val, hy]
        exact algebraMap_eq_factorUnit_mul_parameter_pow_fibre q u P j)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ r : MaximalSpectrum C, IsNoetherianRing (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, Ring.KrullDimLE 1 (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime r.asIdeal))]
  [∀ q : MaximalSpectrum B, Fintype
    (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))] in
/-- **A tame-symbol preparation over `B` gives a simultaneous power factorization of the family in
every local ring of `C`.** The maximal ideals of `C` are the maximal ideals of the
semilocalizations `C_𝔮`, and at such a one the parameter of the preparation at `𝔮` stays a
nonzerodivisor and its unit parts stay units. This is the witness that makes the data hypotheses
of `Stacks.Chow.preparationSymbolValue_eq_prod_norm_factorizationValue` non-vacuous. -/
theorem exists_factorization_localizationAtPrime
    (hfass : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (r : MaximalSpectrum C) :
    ∃ (π : Localization.AtPrime r.asIdeal)
      (_ : π ∈ nonZeroDivisors (Localization.AtPrime r.asIdeal))
      (w : Fin n → (Localization.AtPrime r.asIdeal)ˣ) (e : Fin n → ℕ),
      ∀ k, algebraMap A (Localization.AtPrime r.asIdeal) (a k) =
        (w k : Localization.AtPrime r.asIdeal) * π ^ e k := by
  obtain ⟨⟨q, u⟩, h⟩ : ∃ s, maximalSpectrumSigmaEquiv B C s = r :=
    ⟨_, (maximalSpectrumSigmaEquiv B C).apply_symm_apply r⟩
  subst h
  exact ⟨algebraMap (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (u.asIdeal.under C)) (P.parameter q.asIdeal),
    mem_nonZeroDivisors_algebraMap_fibre q (hfass q) u (parameter_mem_nonZeroDivisors P q),
    fun k => Units.map (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom (P.factorUnit q.asIdeal k),
    fun k => P.exponent q.asIdeal k,
    fun k => algebraMap_eq_factorUnit_mul_parameter_pow_fibre q u P k⟩

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ r : MaximalSpectrum C, IsNoetherianRing (Localization.AtPrime r.asIdeal)]
  [∀ r : MaximalSpectrum C, Ring.KrullDimLE 1 (Localization.AtPrime r.asIdeal)] in
/-- **The second half of Stacks 0EAR at one maximal ideal `𝔮` of `B`, for the pushed-forward
factorization.** The product over the maximal ideals of `C` above `𝔮` of the residue-field norms
down to `κ(𝔪)` of the factor of the formula Stacks 0EAQ computed from the factorization that a
tame-symbol preparation over `B` induces there is the norm down to `κ(𝔪)` of the factor at `𝔮`
itself.

Transitivity of norms for `κ(𝔯)/κ(𝔮)/κ(𝔪)` (Stacks 0BIJ) replaces each outer norm by a norm down
to `κ(𝔮)` followed by the norm of `κ(𝔮)/κ(𝔪)`, and the resulting inner product collapses onto the
factor at `𝔮` by `Stacks.Chow.prod_norm_factorizationValue_algebraMap`. No tame symbol enters:
this is a statement about the formula alone. -/
theorem prod_units_map_norm_factorizationValue_fibre
    (q : MaximalSpectrum B)
    (hfass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfinj : Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hfquot : ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
      LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n) :
    ∏ u : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime (fibrePoint q u).asIdeal) →* ResidueField A)
          (factorizationValue
            (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (u.asIdeal.under C)) (P.parameter q.asIdeal))
            (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom
              (P.factorUnit q.asIdeal i))
            (Units.map (algebraMap (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime (u.asIdeal.under C))).toMonoidHom
              (P.factorUnit q.asIdeal j))
            (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)) =
      Units.map (Algebra.norm (ResidueField A) :
          ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
        (preparationSymbolFactor P q.asIdeal i j) := by
  have hfactor : preparationSymbolFactor P q.asIdeal i j =
      factorizationValue (P.parameter q.asIdeal) (P.factorUnit q.asIdeal i)
        (P.factorUnit q.asIdeal j) (P.exponent q.asIdeal i) (P.exponent q.asIdeal j) := rfl
  rw [hfactor, ← prod_norm_factorizationValue_algebraMap q hfass hfinj hfquot
    (parameter_mem_nonZeroDivisors P q)
    (P.factorUnit q.asIdeal i) (P.factorUnit q.asIdeal j) (P.exponent q.asIdeal i)
    (P.exponent q.asIdeal j), map_prod]
  refine Finset.prod_congr rfl fun u _ => ?_
  have htower := isScalarTower_localizationAtPrime_under (A := A) q u
  have hlocal : IsLocalHom (algebraMap A (Localization.AtPrime (u.asIdeal.under C))) :=
    inferInstanceAs (IsLocalHom (algebraMap A (Localization.AtPrime (fibrePoint q u).asIdeal)))
  rw [units_map_norm_residueField_comp (A := A) (B := Localization.AtPrime q.asIdeal)]

omit [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)] in
/-- **Stacks 0EAT at one maximal ideal `𝔮` of `B`.** The product over the maximal ideals of `C`
above `𝔮` of the residue-field norms down to `κ(𝔪)` of the symbols there is the norm down to
`κ(𝔪)` of the symbol at `B_𝔮` itself.

Transitivity of norms for `κ(𝔯)/κ(𝔮)/κ(𝔪)` (Stacks 0BIJ) replaces each outer norm by a norm down
to `κ(𝔮)` followed by the norm of `κ(𝔮)/κ(𝔪)`, and the resulting inner product collapses onto the
factor at `𝔮` by `Stacks.Chow.prod_norm_factorizationValue_algebraMap`, the second half of Stacks
0EAR. -/
theorem prod_units_map_norm_tameSymbol_fibre
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (symbC : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    (q : MaximalSpectrum B)
    (hfass : ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfinj : Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hfquot : ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
      LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    ∏ u : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)),
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime (fibrePoint q u).asIdeal) →* ResidueField A)
          (symbC (fibrePoint q u) (toExtensionNonZeroDivisor hC (fibrePoint q u) x)
            (toExtensionNonZeroDivisor hC (fibrePoint q u) y)) =
      Units.map (Algebra.norm (ResidueField A) :
          ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
        (preparationSymbolFactor P q.asIdeal i j) := by
  rw [← prod_units_map_norm_factorizationValue_fibre q hfass hfinj hfquot P i j]
  exact Finset.prod_congr rfl fun u _ =>
    congrArg _ (tameSymbol_fibre_eq_factorizationValue hC symbC q hfass u P i j x y hx hy)

/-- **Stacks 0EAT, with no refinement on the right-hand side.** Let `(A, 𝔪)` be a one-dimensional
Noetherian local ring, let `A ⊆ B` be a finite ring extension with `𝔪` not an associated prime of
`B`, let `a, b ∈ A` be nonzerodivisors and let `B ⊆ C` be a further finite extension. Then

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product being over the maximal ideals `𝔮` of `B`, where `∂_A` is the norm pushforward to `A`
of an arbitrary family of tame symbols on the local rings of `C` — the recipe of Stacks 0EAQ
computed over the refinement `C` — and `∂_{B_𝔮}` is an arbitrary tame symbol on `B_𝔮` in the
sense of Stacks 0EAH. Nothing on the right-hand side mentions `C`.

The hypothesis that makes the right-hand side evaluable is a tame-symbol preparation of `a, b`
over `B` (Stacks 0EAG): a tame symbol on a local ring is pinned down on a pair admitting a
simultaneous power factorization, so the preparation determines `∂_{B_𝔮}(a, b)` for every tame
symbol on `B_𝔮`, and its image in `C_𝔯` determines `∂_{C_𝔯}(a, b)` likewise.

This is the source's proof. The maximal ideals of `C` are the `𝔪_{𝔮, v}` lying over the maximal
ideals `𝔮` of `B`, by `Stacks.Localization.prod_maximalSpectrum_eq_prod_prod`; transitivity of
norms for `κ(𝔪_{𝔮, v})/κ(𝔮)/κ(𝔪)` (Stacks 0BIJ) regroups the product over the maximal ideals of
`C` into an iterated product; and the inner product collapses onto the factor at `𝔮` by the
second half of Stacks 0EAR, `Stacks.Chow.prod_norm_factorizationValue_algebraMap`. -/
theorem normProd_eq_prod_norm_tameSymbol
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfass : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfinj : ∀ q : MaximalSpectrum B, Function.Injective
      (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hfquot : ∀ q : MaximalSpectrum B, ∃ n : ℕ,
      maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (symbB : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (symbC : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normProd hC symbC x y =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (symbB q (toExtensionNonZeroDivisor hB q x) (toExtensionNonZeroDivisor hB q y)) := by
  rw [normProd_eq, prod_maximalSpectrum_eq_prod_prod B C]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [preparationSymbolFactor_eq_tameSymbol P q.asIdeal (symbB q) i j
    (toExtensionNonZeroDivisor hB q x) (toExtensionNonZeroDivisor hB q y)
    (by rw [toExtensionNonZeroDivisor_val, hx]) (by rw [toExtensionNonZeroDivisor_val, hy])]
  exact prod_units_map_norm_tameSymbol_fibre hC symbC q (hfass q) (hfinj q) (hfquot q)
    P i j x y hx hy

omit [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)] in
/-- **Stacks 0EAR for the choice of the auxiliary extension, along a tower.** The recipe of
Stacks 0EAQ for a tame-symbol preparation over `B` gives the same element of `κ(𝔪)^*` as the norm
pushforward to `A` of any family of tame symbols on the local rings of a further finite extension
`B ⊆ C` — that is, refining the auxiliary extension does not change the value of the formula.

With `Stacks.Chow.preparationSymbolValue_eq_of_preparations`, which is Stacks 0EAR for the choice
of the local factorizations at a fixed extension, this is the second of the two independence
assertions of Stacks 0EAR, in the case of a refinement. Independence for two auxiliary extensions
`B` and `B'` neither of which refines the other is
`Stacks.Chow.preparationSymbolValue_eq_of_extensions`, which compares them through the common
refinement `Stacks.Chow.TorsionCommonRefinement`. -/
theorem normProd_eq_preparationSymbolValue
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfass : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfinj : ∀ q : MaximalSpectrum B, Function.Injective
      (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hfquot : ∀ q : MaximalSpectrum B, ∃ n : ℕ,
      maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (symbC : ∀ r : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime r.asIdeal))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normProd hC symbC x y = preparationSymbolValue P i j := by
  rw [normProd_eq, prod_maximalSpectrum_eq_prod_prod B C,
    show preparationSymbolValue P i j =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (preparationSymbolFactor P q.asIdeal i j) from rfl]
  exact Finset.prod_congr rfl fun q _ =>
    prod_units_map_norm_tameSymbol_fibre hC symbC q (hfass q) (hfinj q) (hfquot q) P i j x y hx hy

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)] in
/-- **The recipe of Stacks 0EAQ over `B`, recomputed over a refinement `C` of `B`.** Let `(A, 𝔪)`
be a one-dimensional Noetherian local ring, let `A ⊆ B` be a finite extension and `B ⊆ C` a
further finite one, and fix at each maximal ideal `𝔯` of `C` a simultaneous power factorization
`a k = w_{k, 𝔯} π_𝔯^{e_{k, 𝔯}}` of the family `a` — the data of Stacks 0EAG at the extension `C`.
Then the value of the formula Stacks 0EAQ computed from a tame-symbol preparation over `B` is the
value of that formula computed from the data over `C`:

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(factor at 𝔮) = ∏_𝔯 Norm_{κ(𝔯)/κ(𝔪)}(factor at 𝔯)`.

Two steps, both already available. The maximal ideals of `C` are the maximal ideals of the
semilocalizations `C_𝔮` (`Stacks.Localization.prod_maximalSpectrum_eq_prod_prod`), so the
right-hand product regroups into an iterated one; and in each `C_𝔯` the fixed factorization and
the one pushed forward from `B_𝔮` factorize the same pair, hence give the same factor by
`Stacks.Chow.factorizationValue_eq_of_factorizations` — the first half of Stacks 0EAR — after
which the inner product collapses onto the factor at `𝔮` by
`Stacks.Chow.prod_units_map_norm_factorizationValue_fibre`.

Nothing in the right-hand side mentions `B`, so this is what makes the recipe independent of the
auxiliary extension: two extensions `B`, `B'` with a common refinement `C` both compute the value
over `C`. -/
theorem preparationSymbolValue_eq_prod_norm_factorizationValue
    (hfass : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hfinj : ∀ q : MaximalSpectrum B, Function.Injective
      (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hfquot : ∀ q : MaximalSpectrum B, ∃ n : ℕ,
      maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B)
    (π : ∀ r : MaximalSpectrum C, Localization.AtPrime r.asIdeal)
    (hπ : ∀ r : MaximalSpectrum C, π r ∈ nonZeroDivisors (Localization.AtPrime r.asIdeal))
    (w : ∀ r : MaximalSpectrum C, Fin n → (Localization.AtPrime r.asIdeal)ˣ)
    (e : ∀ _r : MaximalSpectrum C, Fin n → ℕ)
    (hfac : ∀ (r : MaximalSpectrum C) (k : Fin n),
      algebraMap A (Localization.AtPrime r.asIdeal) (a k) =
        (w r k : Localization.AtPrime r.asIdeal) * π r ^ e r k)
    (i j : Fin n) :
    preparationSymbolValue P i j =
      ∏ r : MaximalSpectrum C,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime r.asIdeal) →* ResidueField A)
          (factorizationValue (π r) (w r i) (w r j) (e r i) (e r j)) := by
  rw [prod_maximalSpectrum_eq_prod_prod B C,
    show preparationSymbolValue P i j =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (preparationSymbolFactor P q.asIdeal i j) from rfl]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← prod_units_map_norm_factorizationValue_fibre q (hfass q) (hfinj q) (hfquot q) P i j]
  refine Finset.prod_congr rfl fun u _ => ?_
  have : IsNoetherianRing (Localization.AtPrime (u.asIdeal.under C)) :=
    inferInstanceAs (IsNoetherianRing (Localization.AtPrime (fibrePoint q u).asIdeal))
  have : Ring.KrullDimLE 1 (Localization.AtPrime (u.asIdeal.under C)) :=
    inferInstanceAs (Ring.KrullDimLE 1 (Localization.AtPrime (fibrePoint q u).asIdeal))
  exact congrArg _ (factorizationValue_eq_of_factorizations
    (mem_nonZeroDivisors_algebraMap_fibre q (hfass q) u (parameter_mem_nonZeroDivisors P q))
    (hπ (fibrePoint q u))
    (algebraMap_eq_factorUnit_mul_parameter_pow_fibre q u P i)
    (algebraMap_eq_factorUnit_mul_parameter_pow_fibre q u P j)
    (hfac (fibrePoint q u) i) (hfac (fibrePoint q u) j))

end Tower

end Stacks.Chow

end
