module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hilbert–Samuel degree `d(M)` of a module

Let `(R, m)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition, that is an ideal
with `√I = m`, and let `M` be a finite `R`-module. The function
`χ_{I,M} : n ↦ length_R (M / I ^ (n + 1) M)` is a numerical polynomial; `d(M)` is its degree for
`I = m`, an element of `{-∞, 0, 1, 2, …} = WithBot ℕ`, equal to `-∞` exactly when `M = 0`.

## Main definitions

* `Ideal.hilbertSamuelDegree`: the degree of the numerical polynomial
  `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`, an element of `{-∞, 0, 1, 2, …}`, for an ideal
  `I ⊆ R` and an `R`-module `M`.
* `Module.hilbertSamuelDegree`: the invariant `d(M)`, that is `Ideal.hilbertSamuelDegree` for the
  maximal ideal of a local ring `R`.
* `IsIdealOfDefinition`: an ideal of a Noetherian local ring whose radical is the maximal ideal.
* `hilbertSamuel_chi`: the function `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`, valued in `ℕ∞`.

## Main results

* `chi_change_ideal_of_definition`: for ideals of definition `I, I'` and a finite `R`-module `M`
  there is `a > 0` with `χ_{I,M}(n) ≤ χ_{I',M}(a·n)` for all `n ≥ 1`.

## Tags

Hilbert–Samuel function, numerical polynomial, degree, Noetherian local ring, length
-/

@[expose] public section

@[expose] public section

open Filter IsLocalRing Polynomial

/-- The degree, an element of `{-∞, 0, 1, 2, …} = WithBot ℕ`, of the numerical polynomial
`χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`: the degree of a polynomial `P ∈ ℚ[t]` with
`P(n) = χ_{I,M}(n)` for all `n ≫ 0`, and `-∞` if there is no such polynomial. -/
@[stacks 00KA "Definition 00KA is the case `I = maximalIdeal R`, spelled
`Module.hilbertSamuelDegree`. The definition is stated for an arbitrary ideal because that is the
generality of the surrounding section, and because Lemma 00K9(2) is the assertion that this value
is the same for all ideals of definition.", ega "0 16.2.3"]
public noncomputable def Ideal.hilbertSamuelDegree {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] : WithBot ℕ :=
  open Classical in
  (if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        P.eval (n : ℚ) = (p : ℚ) then h.choose else 0).degree

/-- The invariant `d(M) ∈ {-∞, 0, 1, 2, …} = WithBot ℕ` of a module `M` over a local ring
`(R, m)`: the degree of the numerical polynomial `χ_M(n) = length_R (M / m ^ (n + 1) M)`, that is
`Ideal.hilbertSamuelDegree` at the maximal ideal. -/
@[stacks 00KA "The `d(M)` of the definition. Case (1) is not a separate branch: for `M = 0` the
polynomial computing `χ_M` is `0`, whose degree is `-∞ = ⊥`, and conversely a computing
polynomial of degree `-∞` forces `M = m ^ n M` for `n ≫ 0`, hence `M = 0` by Nakayama. See the
module docstring.", ega "0 16.2.3" "special case"]
public noncomputable abbrev Module.hilbertSamuelDegree (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : WithBot ℕ :=
  (maximalIdeal R).hilbertSamuelDegree M

end

end

/-!
## Changing the ideal of definition
-/

@[expose] public section

/-- An ideal `I` of a local ring `(R, m)` is an *ideal of definition* if its
radical equals the maximal ideal `m`, i.e. `√I = m`. -/
@[ega "0 16.2.1", ega "III 4.3.13", ega "IV 21.13.12.1", ega "IV 6.1.3", sga "1 I 2.1"]
def IsIdealOfDefinition' {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

/-- The function `χ_{I,M}(n) = length_R (M / I^{n+1} M)`, valued in `ℕ∞`, where `I^{n+1} M` is
the submodule `I^(n+1) • ⊤` of `M`. -/
noncomputable def hilbertSamuel_chi {R : Type*} [CommRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))

/-- Let `(R, m)` be a Noetherian local ring, let `I, I'` be two ideals of definition
of `R`, and let `M` be a finite `R`-module. Then there exists a positive integer
`a` such that
  `χ_{I,M}(n) ≤ χ_{I',M}(a·n)` for all `n ≥ 1`. -/
@[stacks 00K7]
theorem chi_change_ideal_of_definition
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I I' : Ideal R) (hI : IsIdealOfDefinition' I) (hI' : IsIdealOfDefinition' I') :
    ∃ a : ℕ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n → hilbertSamuel_chi I M n ≤ hilbertSamuel_chi I' M (a * n) := by
  have hrad : I' ≤ I.radical := Ideal.le_radical.trans (hI'.trans hI.symm).le
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing I')
  obtain ⟨c', hc'pos, hc'⟩ : ∃ c', 1 ≤ c' ∧ I' ^ c' ≤ I :=
    ⟨max c 1, le_max_right c 1, le_trans (Ideal.pow_le_pow_right (le_max_left c 1)) hc⟩
  refine ⟨2 * c' - 1, ?_, ?_⟩
  · omega
  intro n hn
  have hexp : c' * (n + 1) ≤ (2 * c' - 1) * n + 1 := by
    obtain ⟨e, rfl⟩ : ∃ e, c' = e + 1 := ⟨c' - 1, by omega⟩
    rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega]
    nlinarith
  have hkey : I' ^ ((2 * c' - 1) * n + 1) ≤ I ^ (n + 1) := by
    calc I' ^ ((2 * c' - 1) * n + 1)
        ≤ I' ^ (c' * (n + 1)) := Ideal.pow_le_pow_right hexp
      _ = (I' ^ c') ^ (n + 1) := by rw [← pow_mul]
      _ ≤ I ^ (n + 1) := Ideal.pow_right_mono hc' (n + 1)
  have hsmul : I' ^ ((2 * c' - 1) * n + 1) • (⊤ : Submodule R M)
      ≤ I ^ (n + 1) • (⊤ : Submodule R M) := Submodule.smul_mono hkey le_rfl
  exact Module.length_le_of_surjective _ (Submodule.factor_surjective hsmul)

end

@[expose] public section

/-- An ideal `I` of a Noetherian local ring `(R, m)` is an *ideal of definition* if its
radical is the maximal ideal, i.e. `√I = m`. -/
@[stacks 07DU,
  ega "0 16.2.1",
  ega "0 7.1.2" "special case",
  ega "III 4.3.13",
  ega "IV 21.13.12.1",
  ega "IV 6.1.3", sga "1 I 2.1"]
def IsIdealOfDefinition {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

/-- Unfolding of `IsIdealOfDefinition`: `I` is an ideal of definition exactly when its
radical is the maximal ideal. -/
@[ega "0 16.2.1" "special case"]
theorem isIdealOfDefinition_iff {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsIdealOfDefinition I ↔ I.radical = IsLocalRing.maximalIdeal R :=
  Iff.rfl

end
