module

public import StacksFrontier.RingTheory.DedekindDomain.DerivationValuation
public import StacksFrontier.RingTheory.Derivation.FormallyEtaleExtension
public import StacksFrontier.RingTheory.Polynomial.ValuationRingAtInfinity

/-!
# Finite extensions of `k[X]` carrying an extension of `d/dX`

Let `k` be an algebraically closed field of characteristic zero and `B` a domain which is finite
and torsion free over `k[X]`. Suppose `B` carries a `k`-derivation `D` with `D X = 1` whose
constants are `k`. Then `B = k[X]`.

The proof looks at the point at infinity. Put `K = Frac k[X]`, `L = Frac B`, `s = X⁻¹`, and let
`O` be the integral closure in `L` of the ring `A∞ ⊆ K` of rational functions regular at infinity;
`O` is a Dedekind domain whose height one primes all contain `s`. The derivation `D` extends to
`L`, and `θ = X • D` is a `k`-derivation of `L` with `θ s = -s`. In characteristic zero such a
logarithmic derivation preserves every valuation ring above infinity
(`IsDedekindDomain.HeightOneSpectrum.valuation_derivation_le_one`), so `θ` maps `O` into itself.
For `z ∈ B` with `s ^ (m + 1) z ∈ O` the identity
`s ^ m D z = θ (s ^ (m + 1) z) + (m + 1) s ^ (m + 1) z` then gives `s ^ m D z ∈ O`: the derivation
lowers the order of the pole at infinity. An element of `B ∩ O` has a minimal polynomial over `K`
with coefficients in `k[X] ∩ A∞ = k`, so it lies in `k`. By induction on the order of the pole,
using antiderivatives in characteristic zero and that the constants of `D` are `k`, every element
of `B` is a polynomial in `X`.

## Main results

* `Polynomial.surjective_algebraMap_of_derivation`: the statement above.
-/

@[expose] public section

open Polynomial IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra

namespace Polynomial

/-- In characteristic zero every polynomial has an antiderivative. -/
theorem exists_derivative_eq {k : Type*} [Field k] [CharZero k] (f : k[X]) :
    ∃ g : k[X], derivative g = f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨g, rfl⟩ := hp
    obtain ⟨h, rfl⟩ := hq
    exact ⟨g + h, derivative_add⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [derivative_monomial]
    congr 1
    push_cast
    field_simp

/-- A derivation with `D X = 1` acts on polynomials in `X` as `d/dX`. -/
theorem derivation_algebraMap_of_apply_X_eq_one {k B : Type*} [Field k] [CommRing B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] (D : Derivation k B B)
    (hD : D (algebraMap k[X] B X) = 1) (g : k[X]) :
    D (algebraMap k[X] B g) = algebraMap k[X] B (derivative g) := by
  have h (f : k[X]) : algebraMap k[X] B f = aeval (algebraMap k[X] B X) f := by
    rw [aeval_algebraMap_apply, aeval_X_left_apply]
  rw [h g, Derivation.map_aeval, hD, smul_eq_mul, mul_one, ← h]

/-- **A bound for a derivation on a finite extension.** Let `S` be finite over `R` with fraction
field `L`, and `δ` a derivation of `L` preserving `R`. Then a single nonzero `c ∈ S` clears the
denominators of `δ` on all of `S`. -/
theorem _root_.Derivation.exists_mul_mem_range_of_finite {R S L k : Type*} [CommRing R]
    [CommRing S] [IsDomain S] [Field L] [CommRing k] [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsFractionRing S L] [Module.Finite R S] [Algebra k L]
    (δ : Derivation k L L) (hδ : ∀ r : R, δ (algebraMap R L r) ∈ Set.range (algebraMap R L)) :
    ∃ c : S, c ≠ 0 ∧ ∀ y : S, algebraMap S L c * δ (algebraMap S L y) ∈
      Set.range (algebraMap S L) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors S)
    (G.image fun g ↦ δ (algebraMap S L g))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y ↦ ?_⟩
  have hy : y ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, hn⟩ := hb _ (Finset.mem_image_of_mem _ hg)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁
    obtain ⟨n₂, hn₂⟩ := h₂
    exact ⟨n₁ + n₂, by rw [map_add, map_add, map_add, mul_add, hn₁, hn₂]⟩
  | smul r y _ h =>
    obtain ⟨n, hn⟩ := h
    obtain ⟨r', hr'⟩ := hδ r
    refine ⟨algebraMap R S r * n + b * y * algebraMap R S r', ?_⟩
    rw [Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, map_mul, hn, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, hr', ← hr']
    ring

namespace DerivationFiniteExtension

variable {k : Type*} [Field k] (B : Type*) [CommRing B] [IsDomain B] [Algebra k[X] B]
  [Algebra k B] [IsScalarTower k k[X] B] [FaithfulSMul k[X] B]

local notation "K" => FractionRing k[X]
local notation "L" => FractionRing B
local notation "A∞" => AtInfinity k
local notation "O" => integralClosure (AtInfinity k) (FractionRing B)

/-- `L = Frac B` as an algebra over the ring `A∞` at infinity, through `K = Frac k[X]`. -/
noncomputable instance : Algebra (AtInfinity k) (FractionRing B) :=
  ((algebraMap K L).comp (algebraMap (AtInfinity k) K)).toAlgebra

/-- The tower `A∞ → K → L`. -/
instance : IsScalarTower (AtInfinity k) K L := .of_algebraMap_eq fun _ ↦ rfl

/-- The tower `k → A∞ → L`. -/
instance : IsScalarTower k (AtInfinity k) L := .of_algebraMap_eq fun c ↦ by
  rw [IsScalarTower.algebraMap_apply (AtInfinity k) K L,
    ← IsScalarTower.algebraMap_apply k (AtInfinity k) K, ← IsScalarTower.algebraMap_apply k K L]

variable [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]

/-- `L` is the fraction field of the integral closure `O` of `A∞` in `L`. -/
instance : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A∞ K L O

variable [CharZero k]

/-- The integral closure `O` of `A∞` in `L` is a Dedekind domain. -/
instance : IsDedekindDomain O := IsIntegralClosure.isDedekindDomain A∞ K L O

/-- The integral closure `O` of `A∞` in `L` is finite over `A∞`. -/
instance : Module.Finite A∞ O := IsIntegralClosure.finite A∞ K L O

variable {B}

/-- The element `X` of `L`. -/
noncomputable abbrev xL (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k[X] B]
    [FaithfulSMul k[X] B] : FractionRing B := algebraMap k[X] (FractionRing B) X

/-- The element `s = X⁻¹` of `L`. -/
noncomputable abbrev sL (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k[X] B]
    [FaithfulSMul k[X] B] : FractionRing B :=
  algebraMap (FractionRing k[X]) (FractionRing B) (fracX k)⁻¹

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The image of `X ∈ K` in `L` is `xL`. -/
theorem algebraMap_fracX : algebraMap K L (fracX k) = xL k B :=
  (IsScalarTower.algebraMap_apply k[X] K L X).symm

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The element `X` of `L` is nonzero. -/
theorem xL_ne_zero : xL k B ≠ 0 := by
  rw [← algebraMap_fracX, Ne, map_eq_zero_iff _ (algebraMap K L).injective]
  exact fracX_ne_zero k

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- `s = X⁻¹` in `L`. -/
theorem sL_eq : sL k B = (xL k B)⁻¹ := by
  change algebraMap K L (fracX k)⁻¹ = _
  rw [map_inv₀, algebraMap_fracX]

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- `X * s = 1` in `L`. -/
theorem xL_mul_sL : xL k B * sL k B = 1 := by
  rw [sL_eq, mul_inv_cancel₀ xL_ne_zero]

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The element `s` of `L` is nonzero. -/
theorem sL_ne_zero : sL k B ≠ 0 := by
  rw [sL_eq]
  exact inv_ne_zero xL_ne_zero

/-- The element `s` of `O`. -/
noncomputable abbrev sO (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k[X] B]
    [FaithfulSMul k[X] B] : integralClosure (AtInfinity k) (FractionRing B) :=
  algebraMap (AtInfinity k) _ (AtInfinity.uniformizer k)

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The image of `sO` in `L` is `sL`. -/
theorem algebraMap_sO : algebraMap O L (sO k B) = sL k B := rfl

omit [Algebra k B] [IsScalarTower k k[X] B] in
/-- Every height one prime of `O` lies over the maximal ideal of the ring at infinity. -/
theorem maximalIdeal_le_comap (v : HeightOneSpectrum O) :
    IsLocalRing.maximalIdeal A∞ ≤ v.asIdeal.comap (algebraMap A∞ O) := by
  have : (v.asIdeal.comap (algebraMap A∞ O)).IsMaximal :=
    have := v.isMaximal
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A∞) v.asIdeal
  exact (IsLocalRing.eq_maximalIdeal this).ge

omit [Algebra k B] [IsScalarTower k k[X] B] in
/-- The element `s` lies in every height one prime of `O`. -/
theorem sO_mem (v : HeightOneSpectrum O) : sO k B ∈ v.asIdeal :=
  maximalIdeal_le_comap v AtInfinity.uniformizer_mem_maximalIdeal

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The element `s` of `O` is nonzero. -/
theorem sO_ne_zero : sO k B ≠ 0 := by
  intro h
  have := congrArg (algebraMap O L) h
  rw [algebraMap_sO, map_zero] at this
  exact sL_ne_zero this

/-- An integral element over an algebraically closed field `k` lies in `k`. -/
private theorem mem_range_algebraMap_of_isIntegral {k E : Type*} [Field k] [IsAlgClosed k]
    [Ring E] [IsDomain E] [Algebra k E] {x : E} (hx : IsIntegral k x) :
    x ∈ Set.range (algebraMap k E) :=
  minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx))

/-- **The residue fields of `O` are `k`.** -/
theorem exists_sub_mem [IsAlgClosed k] (v : HeightOneSpectrum O) (y : O) :
    ∃ c : k, y - algebraMap k O c ∈ v.asIdeal := by
  obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := A∞) y
  set φ : O →ₐ[k] O ⧸ v.asIdeal := Ideal.Quotient.mkₐ k v.asIdeal
  have hcoeff (a : A∞) : φ (algebraMap A∞ O a) =
      algebraMap k (O ⧸ v.asIdeal) (AtInfinity.residue k a) := by
    rw [← AlgHom.commutes φ, ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, IsScalarTower.algebraMap_apply k A∞ O, ← map_sub]
    exact maximalIdeal_le_comap v (AtInfinity.sub_residue_mem_maximalIdeal a)
  have hpk : IsIntegral k (φ y) := by
    refine ⟨p.map (AtInfinity.residue k).toRingHom, hp.map _, ?_⟩
    have : eval₂ (algebraMap k (O ⧸ v.asIdeal)) (φ y) (p.map (AtInfinity.residue k).toRingHom) =
        φ (eval₂ (algebraMap A∞ O) y p) := by
      rw [eval₂_map, show φ (eval₂ (algebraMap A∞ O) y p) =
        (φ : O →+* O ⧸ v.asIdeal) (eval₂ (algebraMap A∞ O) y p) from rfl, hom_eval₂]
      congr 1
      ext a
      exact (hcoeff a).symm
    rw [this, hpy, map_zero]
  have : IsDomain (O ⧸ v.asIdeal) := Ideal.Quotient.isDomain _
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isIntegral hpk
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, ← Ideal.Quotient.mkₐ_eq_mk k,
    AlgHom.commutes, hc, sub_self]

/-! ### The extended derivation and the logarithmic derivation `θ = X • D` -/

/-- The fraction field `L` is formally étale over `B`, so derivations of `B` extend to `L`. -/
instance : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)

/-- The extension of `D` to `L = Frac B`. -/
noncomputable def derivL (D : Derivation k B B) : Derivation k L L :=
  Derivation.extendOfFormallyEtale k B L ((Algebra.linearMap B L).compDer D)

omit [IsDomain B] [Algebra k[X] B] [IsScalarTower k k[X] B] [FaithfulSMul k[X] B]
  [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- `derivL D` extends `D`. -/
theorem derivL_algebraMap (D : Derivation k B B) (b : B) :
    derivL D (algebraMap B L b) = algebraMap B L (D b) :=
  Derivation.extendOfFormallyEtale_algebraMap _ b

omit [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
  [CharZero k] in
/-- The image of `X ∈ B` in `L` is `xL`. -/
theorem algebraMap_X_eq_xL : algebraMap B L (algebraMap k[X] B X) = xL k B :=
  (IsScalarTower.algebraMap_apply k[X] B L X).symm

omit [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- The extended derivation sends `X` to `1`. -/
theorem derivL_xL (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1) :
    derivL D (xL k B) = 1 := by
  rw [← algebraMap_X_eq_xL, derivL_algebraMap, hD, map_one]

/-- The logarithmic derivation `θ = X • D` of `L`. -/
noncomputable def theta (D : Derivation k B B) : Derivation k L L := xL k B • derivL D

omit [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- `θ z = X * D z`. -/
theorem theta_apply (D : Derivation k B B) (z : L) : theta D z = xL k B * derivL D z := rfl

omit [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- `D s = -s ^ 2` for `s = X⁻¹`. -/
theorem derivL_sL (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1) :
    derivL D (sL k B) = -(sL k B) ^ 2 := by
  rw [sL_eq, Derivation.leibniz_inv, derivL_xL D hD, smul_eq_mul, mul_one]

omit [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- `θ s = -s`: the derivation `θ` is logarithmic in `s`. -/
theorem theta_sL (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1) :
    theta D (sL k B) = -sL k B := by
  rw [theta_apply, derivL_sL D hD]
  linear_combination (-(sL k B)) * xL_mul_sL (k := k) (B := B)

omit [CharZero k] in
/-- The algebraic identity behind `pow_mul_derivL_eq`. -/
theorem pow_mul_eq_of_mul_eq_one {F : Type*} [Field F] [Algebra k F] (δ : Derivation k F F)
    {x s : F} (hxs : x * s = 1) (hδs : δ s = -s ^ 2) (m : ℕ) (z : F) :
    s ^ m * δ z = x * δ (s ^ (m + 1) * z) + ((m + 1 : ℕ) : F) * (s ^ (m + 1) * z) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hδs, smul_eq_mul, smul_eq_mul, nsmul_eq_mul,
    smul_eq_mul]
  push_cast
  linear_combination (-(s ^ m * δ z) + (m + 1) * s ^ (m + 1) * z) * hxs

omit [IsScalarTower k k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- **The derivation lowers the order of the pole at infinity:**
`s ^ m D z = θ (s ^ (m + 1) z) + (m + 1) s ^ (m + 1) z`. -/
theorem pow_mul_derivL_eq (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1) (m : ℕ)
    (z : L) : sL k B ^ m * derivL D z =
      theta D (sL k B ^ (m + 1) * z) + ((m + 1 : ℕ) : L) * (sL k B ^ (m + 1) * z) :=
  pow_mul_eq_of_mul_eq_one (derivL D) xL_mul_sL (derivL_sL D hD) m z

/-! ### `θ` preserves the integral closure `O` -/

omit [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- `θ` maps the ring `A∞` at infinity into itself. -/
theorem theta_algebraMap_atInfinity (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1)
    (a : A∞) : theta D (algebraMap A∞ L a) ∈ Set.range (algebraMap A∞ L) := by
  obtain ⟨b, hb⟩ := AtInfinity.exists_derivation_eq (theta D) (theta_sL D hD) a
  exact ⟨b, hb.symm⟩

variable [IsAlgClosed k]

/-- **`θ` is integral on `O`:** for every height one prime `v` of `O`, `v (θ y) ≤ 1`. -/
theorem valuation_theta_le_one (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1)
    (v : HeightOneSpectrum O) (y : O) :
    v.valuation L (theta D (algebraMap O L y)) ≤ 1 := by
  obtain ⟨c, hc0, hc⟩ := Derivation.exists_mul_mem_range_of_finite (R := A∞) (S := O)
    (theta D) (theta_algebraMap_atInfinity D hD)
  have hcL : algebraMap O L c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hc0
  have hvc : v.valuation L (algebraMap O L c) ≠ 0 := (Valuation.ne_zero_iff _).mpr hcL
  refine v.valuation_derivation_le_one (exists_sub_mem v) (theta D)
    (M := (v.valuation L (algebraMap O L c))⁻¹) (fun y ↦ ?_) (sO_mem v) sO_ne_zero
    (theta_sL D hD) y
  obtain ⟨n, hn⟩ := hc y
  have he : theta D (algebraMap O L y) = (algebraMap O L c)⁻¹ * algebraMap O L n := by
    rw [hn]
    field_simp
  rw [he, map_mul, map_inv₀]
  exact mul_le_of_le_one_right' (v.valuation_le_one n)

/-- If `s ^ (m + 1) z ∈ O` for `z ∈ B`, then `s ^ m D z ∈ O`. -/
theorem isIntegral_pow_mul_derivL (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1)
    (m : ℕ) {z : L} (hz : IsIntegral A∞ (sL k B ^ (m + 1) * z)) :
    IsIntegral A∞ (sL k B ^ m * derivL D z) := by
  obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := O)).mp hz
  refine (IsIntegralClosure.isIntegral_iff (A := O)).mpr ?_
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one L _ fun v ↦ ?_
  rw [pow_mul_derivL_eq D hD m z, ← hw]
  refine (Valuation.map_add _ _ _).trans (max_le (valuation_theta_le_one D hD v w) ?_)
  rw [map_mul]
  exact mul_le_one' (v.valuation_natCast_le_one _) (v.valuation_le_one w)

/-! ### Elements of `B` without pole at infinity are constant -/

omit [Module.IsTorsionFree k[X] B] [CharZero k] in
/-- **`B ∩ O = k`.** -/
theorem mem_range_of_isIntegral (z : B) (hz : IsIntegral A∞ (algebraMap B L z)) :
    z ∈ Set.range (algebraMap k B) := by
  set zL := algebraMap B L z
  have hX : IsIntegral k[X] zL :=
    (Algebra.IsIntegral.isIntegral (R := k[X]) z).map (IsScalarTower.toAlgHom k[X] B L)
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' K hX
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hz
  set P := minpoly k[X] zL
  have hP (i : ℕ) : ∃ c : k, P.coeff i = C c := by
    refine AtInfinity.eq_C_of_mem_range ⟨(minpoly A∞ zL).coeff i, ?_⟩
    rw [← coeff_map, ← e2, e1, coeff_map]
  have hPk : P = (P.map constantCoeff).map (algebraMap k k[X]) := by
    ext1 i
    obtain ⟨c, hc⟩ := hP i
    rw [coeff_map, coeff_map, hc, constantCoeff_apply, coeff_C_zero, algebraMap_eq]
  have hint : IsIntegral k zL := by
    refine ⟨P.map constantCoeff, (minpoly.monic hX).map _, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap k[X], ← hPk, minpoly.aeval]
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isIntegral hint
  refine ⟨c, IsFractionRing.injective B L ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hc]

/-! ### Every element has a pole of finite order at infinity -/

omit [Algebra k B] [IsScalarTower k k[X] B] [IsAlgClosed k] in
/-- For every `w ∈ L` some `s ^ m w` lies in `O`. -/
theorem exists_isIntegral_pow_mul (w : L) : ∃ m : ℕ, IsIntegral A∞ (sL k B ^ m * w) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) w
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hrad : sO k B ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJ0 : J ≠ ⊥ := fun h ↦ hd0 (by
      rw [h, Ideal.span_le, Set.singleton_subset_iff] at hJ
      exact hJ)
    exact sO_mem ⟨J, hJp, hJ0⟩
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hm
  refine ⟨m, (IsIntegralClosure.isIntegral_iff (A := O)).mpr ⟨e * n, ?_⟩⟩
  have hdL : algebraMap O L d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hd0
  have hs : sL k B ^ m = algebraMap O L e * algebraMap O L d := by
    rw [← algebraMap_sO, ← map_pow, ← he, map_mul]
  rw [hs, map_mul]
  field_simp

end DerivationFiniteExtension

open DerivationFiniteExtension in
/-- **A finite extension of `k[X]` with an extension of `d/dX` whose constants are `k` is `k[X]`.**
Let `k` be an algebraically closed field of characteristic zero and `B` a domain which is finite
and torsion free over `k[X]`. If `D` is a `k`-derivation of `B` with `D X = 1` whose kernel is
`k`, then `k[X] → B` is surjective. -/
theorem surjective_algebraMap_of_derivation {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [FaithfulSMul k[X] B] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B]
    (D : Derivation k B B) (hD : D (algebraMap k[X] B X) = 1)
    (hker : ∀ z, D z = 0 → z ∈ Set.range (algebraMap k B)) :
    Function.Surjective (algebraMap k[X] B) := by
  have key : ∀ (m : ℕ) (z : B), IsIntegral (AtInfinity k) (sL k B ^ m * algebraMap B _ z) →
      z ∈ Set.range (algebraMap k[X] B) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, one_mul] at hz
      obtain ⟨c, rfl⟩ := mem_range_of_isIntegral z hz
      exact ⟨C c, (IsScalarTower.algebraMap_apply k k[X] B c).symm⟩
    | succ m ih =>
      intro z hz
      have h := isIntegral_pow_mul_derivL D hD m hz
      rw [derivL_algebraMap] at h
      obtain ⟨f, hf⟩ := ih (D z) h
      obtain ⟨g, rfl⟩ := exists_derivative_eq f
      obtain ⟨c, hc⟩ := hker (z - algebraMap k[X] B g) (by
        rw [map_sub, derivation_algebraMap_of_apply_X_eq_one D hD, hf, sub_self])
      refine ⟨g + C c, ?_⟩
      rw [map_add, ← algebraMap_eq (R := k), ← IsScalarTower.algebraMap_apply, hc, add_sub_cancel]
  intro z
  obtain ⟨m, hm⟩ := exists_isIntegral_pow_mul (k := k) (algebraMap B (FractionRing B) z)
  exact key m z hm

end Polynomial
