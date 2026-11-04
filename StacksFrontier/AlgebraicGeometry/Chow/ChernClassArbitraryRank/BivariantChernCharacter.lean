module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The Chern character in the rational bivariant ring, and `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) ch(ℰ₂)`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ` be a finite locally free `𝒪_X`-module of no assumed rank. The
Chern character of `ℰ` is

  `ch(ℰ) = ∑_{p ≥ 0} ch_p(ℰ)`,   `ch_p(ℰ) = P_p(ℰ)/p!`,

where `P_p(ℰ)` is the power sum of Stacks 0F9B. The source reads it in `A^*(X) ⊗ 𝐐`. Here the
bivariant ring `A^*(X)` is `Stacks.Chow.TotalChowClass`, the product `∏_{q ≥ 0} A^q(X)` of the
Chow cohomology groups of Stacks 0B7E under the composition of bivariant classes of Stacks 0B75,
and `A^*(X) ⊗ 𝐐` is `Stacks.Chow.rationalTotalChowClass`, that ring tensored over `𝐙` with `𝐐` so
that the factorials become invertible. This file proves the headline conclusion of
[Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D),

  `ch(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ch(ℰ₁) ch(ℰ₂)`,

there, for `ℰ₁` and `ℰ₂` finite locally free of no assumed rank.

## Main definitions

* `Stacks.Chow.rationalTotalChowClass` — the ring `A^*(X) ⊗ 𝐐`.
* `Stacks.Chow.chernCharacterComponentArbitraryRank` — the component `ch_p(ℰ)`.
* `Stacks.Chow.totalChernCharacterArbitraryRank` — the whole of `ch(ℰ)`.

## Main results

* `Stacks.Chow.chernCharacterComponentArbitraryRank_tensorObj` —
  `ch_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁ + p₂ = p} ch_{p₁}(ℰ₁) ch_{p₂}(ℰ₂)`.
* `Stacks.Chow.totalChernCharacterArbitraryRank_tensorObj` — **Stacks 0F9D**, the headline
  identity `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) ch(ℰ₂)`.

## Implementation notes

### Where `ch(ℰ)` lives, and why the variable is only bookkeeping

`Stacks.Chow.TotalChowClass` is a ring and `𝐐` is a commutative `𝐙`-algebra, so
`𝐐 ⊗_𝐙 A^*(X)` is a ring: the products `ch_{p₁}(ℰ₁) ch_{p₂}(ℰ₂)` are formed there, and they are
the compositions of bivariant classes of Stacks 0B75 with rational coefficients.

The sum `∑_{p ≥ 0} ch_p(ℰ)` is infinite — the rank of `ℰ` is unbounded in general, which is the
observation of Stacks 0ESX — so it is not an element of that ring, and `ch(ℰ)` is the *family* of
its components. `PowerSeries A` is the product `∏_{p ≥ 0} A` with the convolution multiplication,
which is exactly the home Stacks 0ESX gives the Chern character, so `ch(ℰ)` is formed as a formal
power series over `A^*(X) ⊗ 𝐐` whose degree-`p` coefficient is `ch_p(ℰ)`. The variable carries no
information beyond the grading, and an identity of two such series is an identity of two Chern
characters holding in every degree at once.

### Why the binomial coefficient disappears

The identity divided by `p!` loses the binomial coefficient of the source exactly because

  `C(p, p₁)/p! = 1/(p₁! p₂!)`   whenever   `p₁ + p₂ = p`,

which is `Nat.add_choose_mul_factorial_mul_factorial`: from `C(p, p₁) · p₂! · p₁! = p!` one gets
that identity in `𝐐`, so the `p₁`-th summand `C(p, p₁) · P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)/p!` is
`(P_{p₁}(ℰ₁)/p₁!) · (P_{p₂}(ℰ₂)/p₂!)`.

## References

* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

section ChernCharacter

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The rational bivariant ring `A^*(X) ⊗ 𝐐`**: the ring `Stacks.Chow.TotalChowClass` of total
Chow cohomology classes, whose multiplication is the composition of bivariant classes of Stacks
0B75, tensored over `𝐙` with `𝐐` so that the factorials `p!` become invertible. The rational
factor is written first, matching `Stacks.Chow.rationalChowCohomologyComponent`. -/
abbrev rationalTotalChowClass : Type (u + 1) := TensorProduct ℤ ℚ (TotalChowClass C sX)

variable (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The degree-`p` component `ch_p(ℰ) = P_p(ℰ)/p!` of the Chern character** of a finite locally
free module of no assumed rank, as an element of the rational bivariant ring `A^*(X) ⊗ 𝐐`. -/
def chernCharacterComponentArbitraryRank (p : ℕ) : rationalTotalChowClass C sX :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] modulePowerSumArbitraryRank C sX E p

/-- **The Chern character `ch(ℰ) = ∑_{p ≥ 0} ch_p(ℰ)`** of a finite locally free module of no
assumed rank, as a formal power series over `A^*(X) ⊗ 𝐐` whose degree-`p` coefficient is
`ch_p(ℰ)`. `PowerSeries A` is the product `∏_{p ≥ 0} A` with the convolution multiplication, which
is the home Stacks 0ESX gives the Chern character. -/
def totalChernCharacterArbitraryRank : PowerSeries (rationalTotalChowClass C sX) :=
  PowerSeries.mk fun p ↦ chernCharacterComponentArbitraryRank C sX E p

/-- The degree-`p` coefficient of `ch(ℰ)` is `ch_p(ℰ)`. -/
@[simp]
theorem coeff_totalChernCharacterArbitraryRank (p : ℕ) :
    PowerSeries.coeff p (totalChernCharacterArbitraryRank C sX E)
      = chernCharacterComponentArbitraryRank C sX E p :=
  PowerSeries.coeff_mk p _

end ChernCharacter

section Tensor

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E₁ E₂ : X.Modules)
  [hE₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
  [hE₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂]

/-- **Stacks 0F9D, the headline identity in each degree.** For `ℰ₁` and `ℰ₂` finite locally free
of no assumed rank and every `p ≥ 0`,

  `ch_p(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∑_{p₁ + p₂ = p} ch_{p₁}(ℰ₁) ch_{p₂}(ℰ₂)`

in `A^*(X) ⊗ 𝐐`. This is `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` divided by `p!`. -/
theorem chernCharacterComponentArbitraryRank_tensorObj (p : ℕ) :
    chernCharacterComponentArbitraryRank C sX (Scheme.Modules.tensorObj E₁ E₂) p
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p,
          chernCharacterComponentArbitraryRank C sX E₁ q.1 *
            chernCharacterComponentArbitraryRank C sX E₂ q.2 := by
  have hns : ∀ (k : ℕ) (a : ℚ) (x : TotalChowClass C sX),
      a ⊗ₜ[ℤ] (k • x) = k • (a ⊗ₜ[ℤ] x) := fun k a x =>
    map_nsmul (TensorProduct.mk ℤ ℚ (TotalChowClass C sX) a) k x
  have hns' : ∀ (k : ℕ) (a : ℚ) (x : TotalChowClass C sX),
      (k • a) ⊗ₜ[ℤ] x = k • (a ⊗ₜ[ℤ] x) := fun k a x =>
    map_nsmul ((TensorProduct.mk ℤ ℚ (TotalChowClass C sX)).flip x) k a
  rw [chernCharacterComponentArbitraryRank,
    modulePowerSumArbitraryRank_tensorObj C sX E₁ E₂ p, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = p := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  rw [chernCharacterComponentArbitraryRank, chernCharacterComponentArbitraryRank,
    Algebra.TensorProduct.tmul_mul_tmul, ← nsmul_eq_mul, hns, ← hns', nsmul_eq_mul]
  have hfac : p.choose q.1 * Nat.factorial q.2 * Nat.factorial q.1 = Nat.factorial p := by
    have h := Nat.add_choose_mul_factorial_mul_factorial q.2 q.1
    rwa [Nat.add_comm q.2 q.1, hq'] at h
  have hfacQ : (p.choose q.1 : ℚ) * (Nat.factorial q.2 : ℚ) * (Nat.factorial q.1 : ℚ)
      = (Nat.factorial p : ℚ) := by exact_mod_cast hfac
  congr 1
  field_simp
  linear_combination hfacQ

/-- **Stacks 0F9D, the headline identity.** Let `(S, δ)` be the situation of Stacks 02QL, let `X`
be locally of finite type over `S` and let `ℰ₁` and `ℰ₂` be finite locally free `𝒪_X`-modules, of
no assumed rank. Then

  `ch(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ch(ℰ₁) ch(ℰ₂)`.

Both sides are power series over the rational bivariant ring `A^*(X) ⊗ 𝐐` whose degree-`p`
coefficient is `ch_p = P_p/p!`; multiplying two such series convolves their coefficients, so this
single identity is `Stacks.Chow.chernCharacterComponentArbitraryRank_tensorObj` in every degree at
once, and that in turn is `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` divided by `p!`. -/
@[stacks 0F9D "the headline equality ch(E_1 tensor E_2) = ch(E_1) ch(E_2), with hypotheses \
EXACTLY the source's: Situation 02QL as the ChowSituation C, X locally of finite type over its \
base, and E_1, E_2 finite locally free O_X-modules -- NO rank is assumed, the predicate being \
AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree and not ...OfRank.  The equality IS read in \
A^*(X) tensor Q: Stacks.Chow.rationalTotalChowClass is the ring Stacks.Chow.TotalChowClass of \
total Chow cohomology classes -- the product over q >= 0 of the groups A^q(X) of Stacks 0B7E, \
whose multiplication is the Cauchy product of the compositions of bivariant classes of Stacks \
0B75 -- tensored over Z with Q so that p! is invertible, so each product ch_{p_1}(E_1) \
ch_{p_2}(E_2) is a composition of bivariant classes with rational coefficients.  ch_p(F) = \
P_p(F)/p! is Stacks.Chow.chernCharacterComponentArbitraryRank and ch(F) itself is \
Stacks.Chow.totalChernCharacterArbitraryRank, the formal power series whose degree-p coefficient \
is ch_p(F): PowerSeries A is the product over p of copies of A under convolution, which is the \
home Stacks 0ESX gives the Chern character, the rank of F being unbounded, so an equality of \
these series is an equality of Chern characters in every degree at once and \
Stacks.Chow.chernCharacterComponentArbitraryRank_tensorObj is that reading.  It is derived from \
the source's more precise equality, Stacks.Chow.modulePowerSumArbitraryRank_tensorObj, by \
dividing by p!: the binomial coefficient disappears because C(p, p_1)/p! = 1/(p_1! p_2!) when \
p_1 + p_2 = p, which is Nat.add_choose_mul_factorial_mul_factorial.  The rank decomposition and \
the splitting principle are PERFORMED by the cited theorem, not supposed; see its note"]
theorem totalChernCharacterArbitraryRank_tensorObj :
    totalChernCharacterArbitraryRank C sX (Scheme.Modules.tensorObj E₁ E₂)
      = totalChernCharacterArbitraryRank C sX E₁ * totalChernCharacterArbitraryRank C sX E₂ := by
  refine PowerSeries.ext fun p => ?_
  rw [PowerSeries.coeff_mul, coeff_totalChernCharacterArbitraryRank]
  simp only [coeff_totalChernCharacterArbitraryRank]
  exact chernCharacterComponentArbitraryRank_tensorObj C sX E₁ E₂ p

end Tensor

end Stacks.Chow

end
