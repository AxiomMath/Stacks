module

public import Mathlib.RingTheory.Norm.Transitivity
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolPreparationValue
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Defs
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FiniteExtension

/-!
# The formula defining the tame symbol, and its independence of the local factorizations

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `a₁, a₂ ∈ A` be nonzerodivisors.
Stacks 0EAG produces a finite ring extension `A ⊆ B` with `B/A` annihilated by a power of `𝔪`,
a nonzerodivisor `π_j ∈ B_j = B_{𝔪_j}` at each maximal ideal of `B`, and factorizations
`a_i = u_{i, j} π_j^{e_{i, j}}` with `u_{i, j}` units of `B_j` — that is a
`AlgebraicGeometry.TameSymbolPreparation`. The formula (Stacks 0EAQ) then reads

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j}e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j)^{m_j}`,  `m_j = length_{B_j}(B_j / π_j B_j)`,

and Stacks 0EAR asserts that the right-hand side depends neither on the local factorizations nor
on `B`.

This file turns that formula into a definition and proves the first of those two independence
assertions.

* `Stacks.Chow.factorizationValue` is the factor at a single maximal ideal, as a genuine function
  of the local data `(π, u₁, u₂, e₁, e₂)`;
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue` is the whole right-hand side of Stacks
  0EAQ, as a genuine function of a preparation;
* `Stacks.Chow.factorizationValue_eq_of_factorizations` and
  `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_sameExtension` are Stacks 0EAR for
  the choice of local factorizations: at a fixed extension `B`, two preparations of the same
  family give the same value.

The argument is the source's. Writing `m = length_B(B/πB)` and `k = length_B(B/θB)` for two
candidate parameters, multiplicativity of the order of vanishing gives `e_i m = k f_i` for
`i = 1, 2`; raising `u₂^{e₁} a₁^{e₂} = u₁^{e₂} a₂^{e₁}` to the `m`-th power and
`v₂^{f₁} a₁^{f₂} = v₁^{f₂} a₂^{f₁}` to the `k`-th power and cancelling the nonzerodivisor
`a₁^{e₂ m}` yields `(u₁^{e₂} u₂^{-e₁})^m = (v₁^{f₂} v₂^{-f₁})^k` already in `B`, hence in
`κ(𝔪)`; and the two signs agree because `m e₁ e₂` is odd exactly when `m`, `e₁` and `e₂` all are,
which by `e_i m = k f_i` happens exactly when `k`, `f₁` and `f₂` all are.

Independence of the choice of `B` is **not** proved here: the source compares two extensions
through `C = (B ⊗_A B') / (𝔪`-power torsion`)`, which needs the glueing of Stacks 0EAE, and then
reduces to the norm-transitivity identity of Stacks 0BIJ. That last identity is available, in the
shape the proof of Stacks 0EAT also needs it, as `Stacks.Chow.prod_units_map_norm_sigma`;
Stacks 0EAT itself is `Stacks.Chow.tameSymbolFormula_eq_finprod_norm`.

## Main definitions

* `Stacks.Chow.factorizationValue` — the factor of the formula Stacks 0EAQ at one maximal ideal.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue` — the right-hand side of Stacks 0EAQ.

## Main results

* `Stacks.Chow.RegularTameSymbol.apply_eq_factorizationValue` — a tame symbol on a local ring
  takes the value `Stacks.Chow.factorizationValue` on a simultaneous power factorization.
* `Stacks.Chow.factorizationValue_eq_of_factorizations` — Stacks 0EAR at one maximal ideal.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_sameExtension` — Stacks 0EAR for the
  choice of local factorizations.
* `Stacks.Chow.normPushforward_apply_eq_symbolValue` — the symbol of Stacks 0EAT, evaluated on a
  preparation, is the value of the formula Stacks 0EAQ.
* `Stacks.Chow.prod_units_map_norm_sigma` — the norm-transitivity step of Stacks 0EAT and of the
  second half of Stacks 0EAR.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0BIJ](https://stacks.math.columbia.edu/tag/0BIJ)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Chow

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The factor of the formula Stacks 0EAQ at a single maximal ideal.** For a nonzerodivisor `π`
of a one-dimensional Noetherian local ring `R`, two units `u`, `v` of `R` and two exponents
`e`, `f`, this is

`((-1)^{e f} ū^f v̄^{-e})^m`,  `m = length_R(R / πR)`,

the value the source attaches to a pair of elements factoring as `u π^e` and `v π^f`. -/
noncomputable def factorizationValue (π : R) (u v : Rˣ) (e f : ℕ) : (ResidueField R)ˣ :=
  ((-1) ^ (e * f) * Units.map (residue R).toMonoidHom u ^ f *
    (Units.map (residue R).toMonoidHom v)⁻¹ ^ e) ^ (Ring.ord R π).toNat

/-- The factor of Stacks 0EAQ with the outer power distributed over the three inner factors. -/
theorem factorizationValue_eq (π : R) (u v : Rˣ) (e f : ℕ) :
    factorizationValue π u v e f =
      (-1) ^ (e * f * (Ring.ord R π).toNat) *
        Units.map (residue R).toMonoidHom u ^ (f * (Ring.ord R π).toNat) *
        (Units.map (residue R).toMonoidHom v)⁻¹ ^ (e * (Ring.ord R π).toNat) := by
  simp only [factorizationValue]
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

/-- **A tame symbol takes the value of the formula Stacks 0EAQ on a simultaneous power
factorization.** This is `Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization` read as a
statement about `Stacks.Chow.factorizationValue`: whatever tame symbol the local ring carries, on
a pair factoring as `u π^e` and `v π^f` it agrees with the formula of the source. -/
theorem RegularTameSymbol.apply_eq_factorizationValue [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (symb : RegularTameSymbol R) (p a b : nonZeroDivisors R) (u v : Rˣ) (e f : ℕ)
    (ha : (a : R) = u * (p : R) ^ e) (hb : (b : R) = v * (p : R) ^ f) :
    symb a b = factorizationValue (p : R) u v e f :=
  symb.apply_eq_of_factorization p a b u v e f ha hb

/-- A square root of `1` has equal powers at exponents of equal parity. -/
private theorem pow_eq_pow_of_mod_two {G : Type*} [Monoid G] {x : G} (hx : x * x = 1)
    {m n : ℕ} (h : m % 2 = n % 2) : x ^ m = x ^ n := by
  have key : ∀ p : ℕ, x ^ p = x ^ (p % 2) := fun p => by
    conv_lhs => rw [← Nat.div_add_mod p 2]
    rw [pow_add, pow_mul, pow_two, hx, one_pow, one_mul]
  rw [key m, key n, h]

omit [IsLocalRing R] in
/-- The order of vanishing of a unit times a power of a nonzerodivisor. -/
private theorem ord_eq_of_factorization {c p : R} (hp : p ∈ nonZeroDivisors R) (w : Rˣ) (n : ℕ)
    (hc : c = w * p ^ n) : Ring.ord R c = n • Ring.ord R p := by
  rw [hc, Ring.ord_mul_of_isUnit_left w.isUnit, Ring.ord_pow hp]

/-- **Stacks 0EAR at a single maximal ideal: the formula Stacks 0EAQ does not depend on the chosen
local factorization.** If the two elements `a₁`, `a₂` of a one-dimensional Noetherian local ring
`R` admit simultaneous power factorizations against two nonzerodivisors `π` and `θ`,

`a₁ = u₁ π^{e₁} = v₁ θ^{f₁}`,  `a₂ = u₂ π^{e₂} = v₂ θ^{f₂}`,

with `u_i`, `v_i` units, then the two values of the formula agree.

This is the source's argument. Multiplicativity of the order of vanishing gives
`e_i m = f_i k` for `m = length_R(R/πR)` and `k = length_R(R/θR)`. Raising
`u₂^{e₁} a₁^{e₂} = u₁^{e₂} a₂^{e₁}` to the `m`-th power and `v₂^{f₁} a₁^{f₂} = v₁^{f₂} a₂^{f₁}`
to the `k`-th power and cancelling the nonzerodivisor `a₁^{e₂ m}` gives
`(u₁^{e₂} u₂^{-e₁})^m = (v₁^{f₂} v₂^{-f₁})^k` already in `R`. The signs agree because
`m e₁ e₂` is odd exactly when each of `m`, `e₁`, `e₂` is, and `e_i m = f_i k` turns that into
the same statement for `k`, `f₁`, `f₂`. -/
@[stacks 0EAR "independence of the choice of the local factorizations, at a single maximal ideal"]
theorem factorizationValue_eq_of_factorizations [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {π θ : R} (hπ : π ∈ nonZeroDivisors R) (hθ : θ ∈ nonZeroDivisors R)
    {a₁ a₂ : R} {u₁ u₂ v₁ v₂ : Rˣ} {e₁ e₂ f₁ f₂ : ℕ}
    (hu₁ : a₁ = u₁ * π ^ e₁) (hu₂ : a₂ = u₂ * π ^ e₂)
    (hv₁ : a₁ = v₁ * θ ^ f₁) (hv₂ : a₂ = v₂ * θ ^ f₂) :
    factorizationValue π u₁ u₂ e₁ e₂ = factorizationValue θ v₁ v₂ f₁ f₂ := by
  rw [factorizationValue_eq, factorizationValue_eq]
  have hord : ∀ {x : R}, x ∈ nonZeroDivisors R → Ring.ord R x = ((Ring.ord R x).toNat : ℕ∞) :=
    fun hx => (ENat.natCast_toNat (Ring.ord_ne_top hx)).symm
  have hordπ := hord hπ
  have hordθ := hord hθ
  generalize (Ring.ord R π).toNat = m at hordπ ⊢
  generalize (Ring.ord R θ).toNat = k at hordθ ⊢
  -- The two length identities `e_i m = f_i k`.
  have hexp : ∀ {c : R} {w w' : Rˣ} {n n' : ℕ},
      c = w * π ^ n → c = w' * θ ^ n' → n * m = n' * k := by
    intro c w w' n n' h h'
    have hord := (ord_eq_of_factorization hπ w n h).symm.trans
      (ord_eq_of_factorization hθ w' n' h')
    have hcast : ((n * m : ℕ) : ℕ∞) = ((n' * k : ℕ) : ℕ∞) := by
      rw [Nat.cast_mul, Nat.cast_mul, ← hordπ, ← hordθ, ← nsmul_eq_mul, ← nsmul_eq_mul]
      exact hord
    exact_mod_cast hcast
  have h₁ : e₁ * m = f₁ * k := hexp hu₁ hv₁
  have h₂ : e₂ * m = f₂ * k := hexp hu₂ hv₂
  -- The unit parts agree already in `R`.
  have hnzd₁ : a₁ ∈ nonZeroDivisors R := by
    rw [hu₁]
    exact mul_mem u₁.isUnit.mem_nonZeroDivisors (pow_mem hπ e₁)
  have cross : ∀ {ρ : R} {w₁ w₂ : Rˣ} {n₁ n₂ N : ℕ}, a₁ = w₁ * ρ ^ n₁ → a₂ = w₂ * ρ ^ n₂ →
      (w₂ : R) ^ (n₁ * N) * a₁ ^ (n₂ * N) = (w₁ : R) ^ (n₂ * N) * a₂ ^ (n₁ * N) := by
    intro ρ w₁ w₂ n₁ n₂ N h₁ h₂
    rw [h₁, h₂]
    ring
  have starm := cross hu₁ hu₂ (N := m)
  have dagger : (v₂ : R) ^ (e₁ * m) * a₁ ^ (e₂ * m) =
      (v₁ : R) ^ (e₂ * m) * a₂ ^ (e₁ * m) := by
    rw [h₁, h₂]
    exact cross hv₁ hv₂
  have hcancel : a₁ ^ (e₂ * m) * ((u₂ : R) ^ (e₁ * m) * (v₁ : R) ^ (e₂ * m)) =
      a₁ ^ (e₂ * m) * ((u₁ : R) ^ (e₂ * m) * (v₂ : R) ^ (e₁ * m)) := by
    linear_combination ((v₁ : R) ^ (e₂ * m)) * starm - ((u₁ : R) ^ (e₂ * m)) * dagger
  have hring : (u₂ : R) ^ (e₁ * m) * (v₁ : R) ^ (e₂ * m) =
      (u₁ : R) ^ (e₂ * m) * (v₂ : R) ^ (e₁ * m) :=
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem hnzd₁ (e₂ * m))).mp hcancel
  have hunit : u₂ ^ (e₁ * m) * v₁ ^ (e₂ * m) = u₁ ^ (e₂ * m) * v₂ ^ (e₁ * m) :=
    Units.ext (by simpa using hring)
  have hres : Units.map (residue R).toMonoidHom u₂ ^ (e₁ * m) *
        Units.map (residue R).toMonoidHom v₁ ^ (e₂ * m) =
      Units.map (residue R).toMonoidHom u₁ ^ (e₂ * m) *
        Units.map (residue R).toMonoidHom v₂ ^ (e₁ * m) := by
    have := congrArg (Units.map (residue R).toMonoidHom) hunit
    simpa only [map_mul, map_pow] using this
  -- The signs agree.
  have hodd : Odd (e₁ * e₂ * m) ↔ Odd (f₁ * f₂ * k) := by
    have h₁' : Odd (e₁ * m) ↔ Odd (f₁ * k) := by rw [h₁]
    have h₂' : Odd (e₂ * m) ↔ Odd (f₂ * k) := by rw [h₂]
    simp only [Nat.odd_mul] at *
    tauto
  have hsign : (-1 : (ResidueField R)ˣ) ^ (e₁ * e₂ * m) = (-1) ^ (f₁ * f₂ * k) := by
    refine pow_eq_pow_of_mod_two (by simp) ?_
    have key : ∀ p q : ℕ, (Odd p ↔ Odd q) → p % 2 = q % 2 := by
      intro p q h
      rw [Nat.odd_iff, Nat.odd_iff] at h
      omega
    exact key _ _ hodd
  have hunits : Units.map (residue R).toMonoidHom u₁ ^ (e₂ * m) *
        (Units.map (residue R).toMonoidHom u₂)⁻¹ ^ (e₁ * m) =
      Units.map (residue R).toMonoidHom v₁ ^ (e₂ * m) *
        (Units.map (residue R).toMonoidHom v₂)⁻¹ ^ (e₁ * m) := by
    rw [inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact hres.symm.trans (mul_comm _ _)
  -- Assembly.
  rw [hsign, ← h₁, ← h₂,
    mul_assoc _ (Units.map (residue R).toMonoidHom u₁ ^ (e₂ * m)),
    mul_assoc _ (Units.map (residue R).toMonoidHom v₁ ^ (e₂ * m)), hunits]

end Local

end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {r : ℕ} {a : Fin r → A}

/-- **The right-hand side of the formula Stacks 0EAQ.** For a tame-symbol preparation of a family
`a` over a one-dimensional Noetherian local ring `A` — a finite extension `A ⊆ B` with local
parameters `π_j` and factorizations `a_i = u_{i,j} π_j^{e_{i,j}}` in `B_j` — and two members `i`,
`j` of the family, this is

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}`,

the product over the maximal ideals of `B`. -/
noncomputable def symbolValue (P : TameSymbolPreparation a B) [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (i j : Fin r) : (ResidueField A)ˣ :=
  ∏ q : MaximalSpectrum B,
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (factorizationValue (P.parameter q.asIdeal) (P.factorUnit q.asIdeal i)
        (P.factorUnit q.asIdeal j) (P.exponent q.asIdeal i) (P.exponent q.asIdeal j))

variable [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

/-- **Stacks 0EAR for the choice of local factorizations.** Two tame-symbol preparations of the
same family over the *same* finite extension `A ⊆ B` differ only in the local parameters, unit
parts and exponents they choose at each maximal ideal of `B`; by
`Stacks.Chow.factorizationValue_eq_of_factorizations` each factor of the formula Stacks 0EAQ is
unchanged, hence so is the product.

Independence of the choice of `B` is not proved; see the module docstring. -/
@[stacks 0EAR "independence of the choice of the local factorizations; independence of the choice
of B is not proved"]
theorem symbolValue_eq_of_sameExtension
    [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    (P P' : TameSymbolPreparation a B) (i j : Fin r) :
    P.symbolValue i j = P'.symbolValue i j := by
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  refine factorizationValue_eq_of_factorizations
    (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal))
    (isRegular_iff_mem_nonZeroDivisors.mp (P'.parameter_isRegular q.asIdeal))
    (P.factorization q.asIdeal i) (P.factorization q.asIdeal j)
    (P'.factorization q.asIdeal i) (P'.factorization q.asIdeal j)

end AlgebraicGeometry.TameSymbolPreparation

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **The symbol of Stacks 0EAT, evaluated on a tame-symbol preparation, is the value of the
formula Stacks 0EAQ.** This identifies the right-hand side of Stacks 0EAT at a prepared extension
with `AlgebraicGeometry.TameSymbolPreparation.symbolValue`, and so ties
`Stacks.Chow.normPushforward` to the formula the source uses to define the tame symbol. -/
theorem normPushforward_apply_eq_symbolValue
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normPushforward hass symb hinj hquot x y = P.symbolValue i j :=
  normPushforward_apply_eq_of_tameSymbolPreparation hass symb hinj hquot P i j x y hx hy

/-- **Transitivity of the norm along a fibred family of residue-field extensions**, which is the
computation the proof of Stacks 0EAT performs and the one the second half of Stacks 0EAR reduces
to. In the source the maximal ideals of the finite extension `C` are indexed as `𝔪_{j, k}`, those
of the intermediate extension `B` as `𝔪_j`, and the identity used is transitivity of norms for
the tower `κ(𝔪_{j,k}) / κ(𝔪_j) / κ(𝔪)` (Fields, Stacks 0BIJ): taking the norm down to `κ(𝔪)` in
one step gives the same answer as taking it to `κ(𝔪_j)` first and multiplying the results.

Here the index set of the maximal ideals of `C` is presented as a sigma type over that of `B`,
which is exactly the correspondence Stacks 0EAE sets up, so the fibrewise regrouping of the
product is the identity on the nose. -/
theorem prod_units_map_norm_sigma (κ : Type*) [Field κ] {J : Type*} [Fintype J]
    (L : J → Type*) [∀ j, Field (L j)] [∀ j, Algebra κ (L j)]
    {K : J → Type*} [∀ j, Fintype (K j)]
    (M : ∀ j, K j → Type*) [∀ j k, Field (M j k)]
    [∀ j k, Algebra (L j) (M j k)] [∀ j k, Algebra κ (M j k)]
    [∀ j k, IsScalarTower κ (L j) (M j k)]
    (x : ∀ j, ∀ k : K j, (M j k)ˣ) :
    ∏ j : J, Units.map (Algebra.norm κ : L j →* κ)
        (∏ k : K j, Units.map (Algebra.norm (L j) : M j k →* L j) (x j k)) =
      ∏ j : J, ∏ k : K j, Units.map (Algebra.norm κ : M j k →* κ) (x j k) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => Units.ext (Algebra.norm_norm ..)

end Stacks.Chow

end
