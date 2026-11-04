module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolPreparationValue

/-!
# Independence of the tame-symbol formula from the chosen factorization

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a₁, a₂ ∈ A` be nonzerodivisors.
A finite extension `A ⊆ B` in which `a₁` and `a₂` become unit multiples of powers of one common
parameter at every maximal ideal of `B` determines the element

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(((-1) ^ (e₁ e₂) ū₁ ^ e₂ ū₂ ^ (-e₁)) ^ m_𝔮)`

of `κ(𝔪)^*`, where `m_𝔮 = length_{B_𝔮}(B_𝔮/π_𝔮 B_𝔮)`. This file proves that the element depends
only on `B`, not on the parameters `π_𝔮`, the units `ū_i` or the exponents `e_i`.

The argument is length arithmetic and a parity count. If `a₁ = u₁ π ^ e₁ = v₁ θ ^ f₁` and
`a₂ = u₂ π ^ e₂ = v₂ θ ^ f₂` in a commutative ring, then comparing lengths through
`length(A/a_i A) = e_i m = f_i k` with `m = length(A/πA)` and `k = length(A/θA)` gives
`e₁ m = f₁ k` and `e₂ m = f₂ k`. Clearing denominators in the two factorizations and cancelling
the nonzerodivisor `a₂` then identifies the unit parts, while `e₁ e₂ m² = f₁ f₂ k²` identifies
the signs, because a natural number and its square have the same parity.

Also proved here is the identity to which comparing two different extensions reduces: for a
finite extension as above, a unit `λ` of `κ(𝔪)` and a nonzerodivisor `x` of `A`,

`λ ^ length_A(A/xA) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(λ) ^ length_{B_𝔮}(B_𝔮/x B_𝔮)`,

which holds because the norm of an element of the base field is its degree-th power and
`length_A(A/xA) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] length_{B_𝔮}(B_𝔮/x B_𝔮)`.

## Main definitions

* `Stacks.Chow.preparationSymbolFactor` — the local factor of the formula at one maximal ideal.
* `Stacks.Chow.preparationSymbolValue` — the product of the norms of those factors.

## Main results

* `Stacks.Chow.factorizationUnit_pow_ord_eq` — two simultaneous power factorizations of the same
  pair of elements of a commutative ring give the same value, as a unit of that ring.
* `Stacks.Chow.factorizationResidue_pow_ord_eq` — the same equality after reduction to the
  residue field of a local ring.
* `Stacks.Chow.preparationSymbolFactor_eq_of_preparations`,
  `Stacks.Chow.preparationSymbolValue_eq_of_preparations` — the local factor and the whole
  product depend only on the extension.
* `Stacks.Chow.pow_ord_toNat_eq_prod_norm_pow` — the norm identity for an element of the base
  residue field.
* `Stacks.Chow.norm_residueField_norm_residueField` — transitivity of the norm for the residue
  fields of a tower of local rings with local structure maps.

## References

* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 0BIJ](https://stacks.math.columbia.edu/tag/0BIJ)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Chow

section OneRing

variable {R : Type u} [CommRing R]

/-- The order of vanishing of a unit multiple of a power of a nonzerodivisor is the exponent
times the order of vanishing of the nonzerodivisor. -/
theorem ord_toNat_unit_mul_pow {p : R} (hp : p ∈ nonZeroDivisors R) (u : Rˣ) (e : ℕ) :
    (Ring.ord R ((u : R) * p ^ e)).toNat = e * (Ring.ord R p).toNat := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit, Ring.ord_pow hp, nsmul_eq_mul, ENat.toNat_mul,
    ENat.toNat_natCast]

/-- A unit multiple of a power of a nonzerodivisor is a nonzerodivisor. -/
theorem unit_mul_pow_mem_nonZeroDivisors {p : R} (hp : p ∈ nonZeroDivisors R) (u : Rˣ) (e : ℕ) :
    (u : R) * p ^ e ∈ nonZeroDivisors R :=
  mul_mem u.isUnit.mem_nonZeroDivisors (pow_mem hp e)

/-- **Stacks 0EAR, independence of the chosen factorization.** Let `a₁` and `a₂` be two elements
of a commutative ring, each written in two ways as a unit times a power of a nonzerodivisor:

`a₁ = u₁ π ^ e₁ = v₁ θ ^ f₁`,  `a₂ = u₂ π ^ e₂ = v₂ θ ^ f₂`.

Then, with `m = length(R/πR)` and `k = length(R/θR)`,

`((-1) ^ (e₁ e₂) u₁ ^ e₂ u₂ ^ (-e₁)) ^ m = ((-1) ^ (f₁ f₂) v₁ ^ f₂ v₂ ^ (-f₁)) ^ k`. -/
theorem factorizationUnit_pow_ord_eq {p θ : R} (hp : p ∈ nonZeroDivisors R)
    (hθ : θ ∈ nonZeroDivisors R) {a₁ a₂ : R} {u₁ u₂ v₁ v₂ : Rˣ} {e₁ e₂ f₁ f₂ : ℕ}
    (hu₁ : a₁ = (u₁ : R) * p ^ e₁) (hu₂ : a₂ = (u₂ : R) * p ^ e₂)
    (hv₁ : a₁ = (v₁ : R) * θ ^ f₁) (hv₂ : a₂ = (v₂ : R) * θ ^ f₂) :
    ((-1) ^ (e₁ * e₂) * u₁ ^ e₂ * u₂⁻¹ ^ e₁) ^ (Ring.ord R p).toNat =
      ((-1) ^ (f₁ * f₂) * v₁ ^ f₂ * v₂⁻¹ ^ f₁) ^ (Ring.ord R θ).toNat := by
  set m := (Ring.ord R p).toNat
  set k := (Ring.ord R θ).toNat
  -- The two factorizations of each `a_i` give the same length, which pins the exponents.
  have hlen : ∀ {a : R} {u v : Rˣ} {e f : ℕ},
      a = (u : R) * p ^ e → a = (v : R) * θ ^ f → e * m = f * k := by
    intro a u v e f hu hv
    rw [← ord_toNat_unit_mul_pow hp u e, ← ord_toNat_unit_mul_pow hθ v f, ← hu, ← hv]
  have h₁ : e₁ * m = f₁ * k := hlen hu₁ hv₁
  have h₂ : e₂ * m = f₂ * k := hlen hu₂ hv₂
  -- Clear the two factorizations of denominators, then raise to the two lengths.
  have hcross : ∀ {w₁ w₂ : Rˣ} {g₁ g₂ : ℕ} {t : R} (n : ℕ),
      a₁ = (w₁ : R) * t ^ g₁ → a₂ = (w₂ : R) * t ^ g₂ →
        (w₂ : R) ^ (g₁ * n) * a₁ ^ (g₂ * n) = (w₁ : R) ^ (g₂ * n) * a₂ ^ (g₁ * n) := by
    intro w₁ w₂ g₁ g₂ t n hw₁ hw₂
    rw [hw₁, hw₂]
    ring
  have hu := hcross m hu₁ hu₂
  have hv : (v₂ : R) ^ (e₁ * m) * a₁ ^ (e₂ * m) = (v₁ : R) ^ (e₂ * m) * a₂ ^ (e₁ * m) := by
    rw [h₁, h₂]
    exact hcross k hv₁ hv₂
  -- Cancelling the nonzerodivisor `a₂` identifies the unit parts.
  have ha₂ : a₂ ∈ nonZeroDivisors R := hu₂ ▸ unit_mul_pow_mem_nonZeroDivisors hp u₂ e₂
  have hunits : (u₁ : R) ^ (e₂ * m) * (v₂ : R) ^ (e₁ * m) =
      (v₁ : R) ^ (e₂ * m) * (u₂ : R) ^ (e₁ * m) := by
    refine mul_cancel_right_mem_nonZeroDivisors (pow_mem ha₂ (e₁ * m)) |>.mp ?_
    linear_combination (u₂ : R) ^ (e₁ * m) * hv - (v₂ : R) ^ (e₁ * m) * hu
  have hgroup : u₁ ^ (e₂ * m) * (u₂ ^ (e₁ * m))⁻¹ = v₁ ^ (e₂ * m) * (v₂ ^ (e₁ * m))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact Units.ext (by simpa using hunits)
  -- A natural number and its square have the same parity, which settles the signs.
  have hsq : e₁ * e₂ * m * m = f₁ * f₂ * k * k := by
    rw [show e₁ * e₂ * m * m = (e₁ * m) * (e₂ * m) by ring, h₁, h₂]
    ring
  have hsign : ((-1 : Rˣ)) ^ (e₁ * e₂ * m) = ((-1 : Rˣ)) ^ (f₁ * f₂ * k) := by
    refine neg_one_pow_congr ?_
    have hmm := congrArg Even hsq
    simp only [Nat.even_mul, eq_iff_iff] at hmm ⊢
    tauto
  rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_mul, hsign, inv_pow, inv_pow, mul_assoc, mul_assoc, hgroup, h₁, h₂, mul_assoc]

variable [IsLocalRing R]

/-- **Stacks 0EAR, independence of the chosen factorization, in the residue field.** The image in
`κ(𝔪)^*` of the value of `Stacks.Chow.factorizationUnit_pow_ord_eq`. -/
theorem factorizationResidue_pow_ord_eq {p θ : R} (hp : p ∈ nonZeroDivisors R)
    (hθ : θ ∈ nonZeroDivisors R) {a₁ a₂ : R} {u₁ u₂ v₁ v₂ : Rˣ} {e₁ e₂ f₁ f₂ : ℕ}
    (hu₁ : a₁ = (u₁ : R) * p ^ e₁) (hu₂ : a₂ = (u₂ : R) * p ^ e₂)
    (hv₁ : a₁ = (v₁ : R) * θ ^ f₁) (hv₂ : a₂ = (v₂ : R) * θ ^ f₂) :
    ((-1) ^ (e₁ * e₂) * Units.map (residue R).toMonoidHom u₁ ^ e₂ *
          (Units.map (residue R).toMonoidHom u₂)⁻¹ ^ e₁) ^ (Ring.ord R p).toNat =
      ((-1) ^ (f₁ * f₂) * Units.map (residue R).toMonoidHom v₁ ^ f₂ *
          (Units.map (residue R).toMonoidHom v₂)⁻¹ ^ f₁) ^ (Ring.ord R θ).toNat := by
  have hneg : Units.map (residue R).toMonoidHom (-1 : Rˣ) = -1 := Units.ext (by simp)
  simpa only [map_pow, map_mul, map_inv, hneg] using
    congrArg (Units.map (residue R).toMonoidHom)
      (factorizationUnit_pow_ord_eq hp hθ hu₁ hu₂ hv₁ hv₂)

end OneRing

section FixedExtension

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {r : ℕ} {a : Fin r → A}

/-- **The local factor of the formula (0EAQ) at one maximal ideal.** For a tame-symbol
preparation of the family `a` and two indices `i`, `j`, this is

`((-1) ^ (e_i e_j) ū_i ^ e_j ū_j ^ (-e_i)) ^ m_𝔮`,  `m_𝔮 = length_{B_𝔮}(B_𝔮/π_𝔮 B_𝔮)`,

a unit of the residue field of `B_𝔮`. -/
noncomputable def preparationSymbolFactor (P : TameSymbolPreparation a B) (q : Ideal B)
    [q.IsMaximal] (i j : Fin r) : (ResidueField (Localization.AtPrime q))ˣ :=
  ((-1) ^ (P.exponent q i * P.exponent q j) *
      Units.map (residue (Localization.AtPrime q)).toMonoidHom (P.factorUnit q i) ^
        P.exponent q j *
      (Units.map (residue (Localization.AtPrime q)).toMonoidHom
        (P.factorUnit q j))⁻¹ ^ P.exponent q i) ^
    (Ring.ord (Localization.AtPrime q) (P.parameter q)).toNat

/-- The local factor is the value any tame symbol on `B_𝔮` takes on the two prepared elements. -/
theorem preparationSymbolFactor_eq_tameSymbol (P : TameSymbolPreparation a B) (q : Ideal B)
    [q.IsMaximal] [IsNoetherianRing (Localization.AtPrime q)]
    [Ring.KrullDimLE 1 (Localization.AtPrime q)]
    (symb : RegularTameSymbol (Localization.AtPrime q)) (i j : Fin r)
    (x y : nonZeroDivisors (Localization.AtPrime q))
    (hx : (x : Localization.AtPrime q) = algebraMap A (Localization.AtPrime q) (a i))
    (hy : (y : Localization.AtPrime q) = algebraMap A (Localization.AtPrime q) (a j)) :
    symb x y = preparationSymbolFactor P q i j :=
  tameSymbol_apply_eq_of_tameSymbolPreparation P q symb i j x y hx hy

/-- **Stacks 0EAR at one maximal ideal.** The local factor of the formula (0EAQ) does not depend
on the preparation: two preparations of the same family over the same extension choose different
parameters, units and exponents, and give the same factor. -/
theorem preparationSymbolFactor_eq_of_preparations (P P' : TameSymbolPreparation a B)
    (q : Ideal B) [q.IsMaximal] (i j : Fin r) :
    preparationSymbolFactor P q i j = preparationSymbolFactor P' q i j := by
  refine factorizationResidue_pow_ord_eq
    (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q))
    (isRegular_iff_mem_nonZeroDivisors.mp (P'.parameter_isRegular q))
    (a₁ := algebraMap A (Localization.AtPrime q) (a i))
    (a₂ := algebraMap A (Localization.AtPrime q) (a j)) ?_ ?_ ?_ ?_ <;>
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
  exacts [P.factorization q i, P.factorization q j, P'.factorization q i, P'.factorization q j]

end FixedExtension

section Value

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  {r : ℕ} {a : Fin r → A}

/-- **The right-hand side of the formula (0EAQ).** The product over the maximal ideals of the
extension of the residue-field norms of the local factors. -/
noncomputable def preparationSymbolValue (P : TameSymbolPreparation a B) (i j : Fin r) :
    (ResidueField A)ˣ :=
  ∏ q : MaximalSpectrum B,
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (preparationSymbolFactor P q.asIdeal i j)

/-- **Stacks 0EAR for a fixed extension.** The formula (0EAQ) does not depend on the chosen local
parameters, units or exponents: two preparations of the same family over the same finite extension
give the same element of `κ(𝔪)^*`. -/
theorem preparationSymbolValue_eq_of_preparations (P P' : TameSymbolPreparation a B)
    (i j : Fin r) : preparationSymbolValue P i j = preparationSymbolValue P' i j :=
  Finset.prod_congr rfl fun q _ =>
    congrArg _ (preparationSymbolFactor_eq_of_preparations P P' q.asIdeal i j)

end Value

section NormOfBaseElement

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B] [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

/-- **The identity to which the comparison of two extensions reduces.** For a one-dimensional
Noetherian local ring `A`, a finite extension `A ⊆ B` with `B / A` annihilated by a power of `𝔪`
and `𝔪` not an associated prime of `B`, a unit `λ` of `κ(𝔪)` and a nonzerodivisor `x` of `A`,

`λ ^ length_A(A/xA) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(λ) ^ length_{B_𝔮}(B_𝔮/x B_𝔮)`.

The norm of an element of `κ(𝔪)` is its `[κ(𝔮) : κ(𝔪)]`-th power, and
`length_A(A/xA) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] length_{B_𝔮}(B_𝔮/x B_𝔮)`. -/
theorem pow_ord_toNat_eq_prod_norm_pow (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (lam : (ResidueField A)ˣ) {x : A} (hx : x ∈ nonZeroDivisors A) :
    lam ^ (Ring.ord A x).toNat =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (Units.map (algebraMap (ResidueField A)
              (ResidueField (Localization.AtPrime q.asIdeal))).toMonoidHom lam ^
            (Ring.ord (Localization.AtPrime q.asIdeal)
              (algebraMap A (Localization.AtPrime q.asIdeal) x)).toNat) := by
  rw [ord_toNat_eq_sum_finrank_mul_ord_toNat hass hinj hquot hx, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_pow, units_map_norm_algebraMap_residueField q lam, ← pow_mul]

end NormOfBaseElement

section ResidueFieldNormTower

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] [IsLocalHom (algebraMap A C)]

/-- Transitivity of the norm at residue fields, on units. -/
theorem units_map_norm_residueField_comp (x : (ResidueField C)ˣ) :
    Units.map (Algebra.norm (ResidueField A) : ResidueField B →* ResidueField A)
        (Units.map (Algebra.norm (ResidueField B) : ResidueField C →* ResidueField B) x) =
      Units.map (Algebra.norm (ResidueField A) : ResidueField C →* ResidueField A) x :=
  Units.ext (Algebra.norm_norm)

end ResidueFieldNormTower

section PowersOfOneParameter

variable {R : Type u} [CommRing R]

/-- **The identity at the pair of parameters `π` and `π ^ n`.** A power of `π` factors both with
respect to `π`, with exponent `n c`, and with respect to `π ^ n`, with exponent `c`; the two
parameters have lengths `length(R/πR)` and `n · length(R/πR)`. -/
theorem factorizationUnit_pow_ord_eq_pow_parameter {p : R} (hp : p ∈ nonZeroDivisors R)
    (n c₁ c₂ : ℕ) (u₁ u₂ : Rˣ) :
    ((-1) ^ (n * c₁ * (n * c₂)) * u₁ ^ (n * c₂) * u₂⁻¹ ^ (n * c₁)) ^ (Ring.ord R p).toNat =
      ((-1) ^ (c₁ * c₂) * u₁ ^ c₂ * u₂⁻¹ ^ c₁) ^ (Ring.ord R (p ^ n)).toNat :=
  factorizationUnit_pow_ord_eq hp (pow_mem hp n)
    (a₁ := (u₁ : R) * p ^ (n * c₁)) (a₂ := (u₂ : R) * p ^ (n * c₂))
    rfl rfl (by rw [← pow_mul]) (by rw [← pow_mul])

/-- The order of vanishing of a power of a nonzerodivisor is the exponent times the order of
vanishing of the nonzerodivisor. -/
theorem ord_toNat_pow {p : R} (hp : p ∈ nonZeroDivisors R) (n : ℕ) :
    (Ring.ord R (p ^ n)).toNat = n * (Ring.ord R p).toNat := by
  simpa using ord_toNat_unit_mul_pow hp 1 n

/-- Over the integers `length(ℤ/2ℤ) = 1` while `length(ℤ/4ℤ) = 2`, so `2` and `2 ^ 2` are
nonzerodivisors with different orders of vanishing. -/
theorem ord_toNat_two_int : (Ring.ord ℤ 2).toNat = 1 ∧ (Ring.ord ℤ (2 ^ 2)).toNat = 2 := by
  have h2 : (2 : ℤ) ∈ nonZeroDivisors ℤ := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have h : (Ring.ord ℤ 2).toNat = 1 := by
    rw [Ring.ord_of_irreducible Int.prime_two.irreducible]
    rfl
  exact ⟨h, by rw [ord_toNat_pow h2, h]⟩

end PowersOfOneParameter

end Stacks.Chow

end
