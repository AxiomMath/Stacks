module

public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Depth is at most the dimension of the support

Proof of `Module.depth_le_supportDim` (Stacks 00LK): for a finite module `M` over a commutative
ring `R` and an ideal `I ⊆ R` with `I • M ≠ M`, one has `depth_I(M) ≤ dim(Supp(M))`.

A weakly `M`-regular sequence `f₁, …, f_r` cuts the dimension of the support down by at least
`r`: since `fᵢ` is a nonzerodivisor on `M/(f₁, …, f_{i-1})M` it avoids every minimal prime of
the annihilator of that module, so
`dim(Supp(M/(f₁, …, f_i)M)) + 1 ≤ dim(Supp(M/(f₁, …, f_{i-1})M))`, and composing the `r` steps
gives `dim(Supp(M/(f₁, …, f_r)M)) + r ≤ dim(Supp(M))`. When the terms lie in `I` the quotient
`M/(f₁, …, f_r)M` is nonzero, because `(f₁, …, f_r)M ≤ I • M ≠ M`, so the left-hand summand is
at least `0` and therefore `r ≤ dim(Supp(M))`. As `depth_I(M)` is by definition the supremum of
these `r` once `I • M ≠ M`, the inequality follows.

Depth takes values in `ℕ∞` and `Module.supportDim` in `WithBot ℕ∞`, the value `⊥` being reserved
for the empty support of the zero module; the comparison is made in `WithBot ℕ∞`. The hypothesis
`I • M ≠ M` forces `M` nonzero, so both sides are honest: `dim(Supp(M)) ≠ ⊥`.

## Main results

* `Stacks.Depth.SupportDimBound.solution`: `depth_I(M) ≤ dim(Supp(M))` for a finite module `M`
  with `I • M ≠ M`.
* `Module.depth_le_ringKrullDim`: the specialisation to `I = 𝔪` and `M = R` over a local ring,
  `depth_𝔪(R) ≤ dim R`.

## Implementation notes

The dimension drop over the whole sequence is isolated as
`supportDim_add_length_le_supportDim_of_isWeaklyRegular`, the inequality
`dim(Supp(M/(f₁, …, f_r)M)) + r ≤ dim(Supp(M))` for a *weakly* regular sequence over an
arbitrary commutative ring. Mathlib has only the equality
`Module.supportDim_add_length_eq_supportDim_of_isRegular`, which assumes `R` Noetherian local
and the sequence regular; neither hypothesis is available here, since the statement is for an
arbitrary ideal of an arbitrary commutative ring. The single-step half of the inequality is
Mathlib's
`Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`, which is already free of both
hypotheses; only the induction over the list was missing.

The supremum defining the depth is reached by unfolding `Module.depth` and discharging its case
distinction with `I • M ≠ M`, not through `Module.depth_eq_iSup_isWeaklyRegular_length`
(Stacks 0AUI): that lemma lives in `StacksFrontier.RingTheory.Depth.Criteria`, which imports this
file for `Module.depth_le_supportDim`, so citing it here would be an import cycle. Unfolding
gives the supremum over *regular* rather than weakly regular sequences, which is all that is
needed — `IsRegular.toIsWeaklyRegular` feeds the dimension drop above.

The source's route is an induction on `dim(Supp(M))` that treats `dim(Supp(M)) = 0` separately
(via 0586, 0587 and 00LL, concluding `Ass(M) = {𝔪}` and hence `depth(M) = 0`) and uses the
equality `dim(Supp(M/f₁M)) = dim(Supp(M)) - 1` of 0B52 in the induction step. Only the
inequality `dim(Supp(M/f₁M)) + 1 ≤ dim(Supp(M))` of that equality is needed, and once the
induction is run on the *sequence* rather than on the dimension the base case is the empty
sequence, where nothing has to be proved. That removes the appeal to 0586, 0587, 00LL and to the
Noetherian local hypothesis at the same time; the mathematics is the source's.

## References

* [StackProject 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

@[expose] public section

namespace Stacks.Depth.SupportDimBound

open RingTheory Sequence

/-- A weakly `M`-regular sequence of length `r` drops the dimension of the support by at least
`r`: `dim Supp(M/(f₁, …, f_r)M) + r ≤ dim Supp(M)`. This is the inequality half of
`Module.supportDim_add_length_eq_supportDim_of_isRegular`, for a weakly regular sequence and
without the hypotheses that `R` be Noetherian local. -/
private theorem supportDim_add_length_le_supportDim_of_isWeaklyRegular {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (rs : List R)
    (reg : IsWeaklyRegular M rs) :
    Module.supportDim R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) + rs.length ≤
      Module.supportDim R M := by
  induction rs generalizing M with
  | nil =>
      simp only [List.length_nil, Nat.cast_zero, add_zero]
      refine le_of_eq (Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot _ ?_))
      simp
  | cons x rs' ih =>
      obtain ⟨hx, hrs'⟩ := (isWeaklyRegular_cons_iff M x rs').mp reg
      have hstep : Module.supportDim R (QuotSMulTop x M) + 1 ≤ Module.supportDim R M :=
        Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
          fun _ => hx.notMem_of_mem_minimalPrimes
      have he : Module.supportDim R (M ⧸ (Ideal.ofList (x :: rs') • ⊤ : Submodule R M)) =
          Module.supportDim R
            (QuotSMulTop x M ⧸ (Ideal.ofList rs' • ⊤ : Submodule R (QuotSMulTop x M))) :=
        Module.supportDim_eq_of_equiv
          (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs')
      rw [he, List.length_cons, Nat.cast_add, Nat.cast_one, ← add_assoc]
      exact le_trans (add_le_add (ih (M := QuotSMulTop x M) hrs') le_rfl) hstep

/-- To bound `depth_I(M)` by `n` when `I • M ≠ M`, it suffices to bound the length of every
`M`-regular sequence in `I`. -/
private theorem depth_le_of_forall_isRegular_length_le {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] (hI : I • (⊤ : Submodule R M) ≠ ⊤) {n : ℕ∞}
    (h : ∀ rs : List R, (∀ r ∈ rs, r ∈ I) → IsRegular M rs → (rs.length : ℕ∞) ≤ n) :
    Module.depth R I M ≤ n := by
  rw [Module.depth, ite_eq_right_of_eq_false _ _ (eq_false hI)]
  exact iSup₂_le fun rs hrs => h rs hrs.1 hrs.2

/-- For a finite `R`-module `M` and an ideal `I` with `I • M ≠ M`, the `I`-depth of `M` is at
most the dimension of the support of `M`: every `M`-regular sequence in `I` has length at most
`dim(Supp(M))`. -/
public theorem solution (R : Type*) [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    (Module.depth R I M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have hM : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with h | h
    · exact absurd (Subsingleton.elim _ _) hI
    · exact h
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (Module.supportDim_ne_bot_of_nontrivial R M)
  -- `I • M ≠ M` puts `depth_I(M)` in the supremum branch of its definition.
  rw [← hd, WithBot.coe_le_coe]
  refine depth_le_of_forall_isRegular_length_le hI fun rs hmem hreg => ?_
  -- `(f₁, …, f_r)M ≤ I • M ≠ M`, so the quotient by the sequence is nonzero.
  have hle : Ideal.ofList rs • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left (Ideal.span_le.mpr hmem)
  have hne : Ideal.ofList rs • (⊤ : Submodule R M) ≠ ⊤ :=
    fun h => hI (top_le_iff.mp (h.symm.trans_le hle))
  have hnt : Nontrivial (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
    (Module.supportDim_ne_bot_of_nontrivial R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)))
  have hkey :=
    supportDim_add_length_le_supportDim_of_isWeaklyRegular rs hreg.toIsWeaklyRegular
  rw [← ha, ← hd] at hkey
  -- The quotient has nonempty support, so its dimension is at least `0`.
  have h0 : (0 : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) := by
    rw [← WithBot.coe_zero]
    exact WithBot.coe_le_coe.mpr zero_le
  refine WithBot.coe_le_coe.mp (le_trans ?_ hkey)
  rw [← zero_add ((rs.length : ℕ∞) : WithBot ℕ∞)]
  exact add_le_add h0 le_rfl

end Stacks.Depth.SupportDimBound

end

/-!
# Depth is at most the dimension of the support

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` a finite `R`-module with `I • M ≠ M`.
Then the `I`-depth of `M` is at most the dimension of the support of `M`,
`depth_I(M) ≤ dim(Supp(M))`. For `(R, 𝔪)` a Noetherian local ring, `I = 𝔪` and `M` nonzero this
is the inequality `dim(Supp(M)) ≥ depth(M)` of the source, the hypothesis `𝔪 • M ≠ M` being
Nakayama's lemma (`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator` applied to
`IsLocalRing.maximalIdeal_le_jacobson`).

The reason is that an `M`-regular sequence `f₁, …, f_r` cuts the dimension of the support down
by at least `r`: each `fᵢ` is a nonzerodivisor on `M/(f₁, …, f_{i-1})M`, hence avoids the
minimal primes of its annihilator, so that
`dim(Supp(M/(f₁, …, f_i)M)) + 1 ≤ dim(Supp(M/(f₁, …, f_{i-1})M))` (Mathlib's
`Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`). The quotient
`M/(f₁, …, f_r)M` is nonzero by the definition of a regular sequence, so its support has
dimension `≥ 0` and therefore `r ≤ dim(Supp(M))`. As `depth_I(M)` is the supremum of these `r`
once `I • M ≠ M`, the inequality follows.

Depth takes values in `ℕ∞` and `Module.supportDim` in `WithBot ℕ∞`, the value `⊥` being
reserved for the empty support of the zero module; the comparison is made in `WithBot ℕ∞`.

## Main results

* `Module.depth_le_supportDim`: `depth_I(M) ≤ dim(Supp(M))` for a finite module `M` with
  `I • M ≠ M`.

## Implementation notes

Faithfulness to [StackProject 00LK]:

1. No dead hypothesis. `I • (⊤ : Submodule R M) ≠ ⊤` cannot be dropped: it is what puts
   `depth_I(M)` in the supremum branch of its definition, and without it the statement is
   false, since `depth_R(M) = ⊤` while `dim(Supp(R))` is `0` for `R` a field, and the depth of
   the zero module is `⊤` while its support is empty of dimension `⊥`. It also supplies the
   source's hypothesis `M ≠ 0`, which is therefore not assumed separately: `I • M ≠ M` forces
   `M` nonzero. `Module.Finite R M` is the source's hypothesis and is used, through the
   description of the support of `M` by the annihilator of `M` on which the dimension drop
   above rests.
2. The scalars are the source's. Both sides are formed over `R` itself: `Module.depth R I M`
   uses sequences in the ideal `I` of `R` and quotients `M/(f₁, …, f_i)M` of the `R`-module
   `M`, and `Module.supportDim R M = krullDim (Module.support R M)` is a dimension of a set of
   primes of `R`. No localisation or base change intervenes.
3. Both quantities are pinned, not merely bounded: the left-hand side is the value of
   `Module.depth R I M` (tag 00LI) and the right-hand side is `Module.supportDim R M`, which is
   `krullDim (Supp(M))` by definition, so the statement compares the two invariants themselves
   rather than asserting the existence of a bound.
4. Not degenerate. For `R = k[[x, y]]`, `I = 𝔪` and `M = R` both sides are `2`, so the
   inequality is sharp; for `M = R/(x) ⊕ R/(x, y)` the left side is `0`, every element of `𝔪`
   being a zerodivisor on `M`, and the right side is `1`, so the inequality is also genuinely
   an inequality; and for `I = (x)` and `M = R` the left side is `1`, so the ideal is not
   inert either.

Three departures from the source's form, none of them weakening it.

The source states the case `I = 𝔪` of the maximal ideal of a local ring, writing `depth(M)`;
the statement here is for an arbitrary ideal `I`, which is the same proof — a regular sequence
in `I` is a regular sequence, and the bound on its length uses nothing about `I`.

The source assumes `R` Noetherian local; neither hypothesis is needed, once "`M` nonzero" is
replaced by the hypothesis `I • M ≠ M` it is used for. Locality and Noetherianity enter the
source's route through the equality `dim(Supp(M/f₁M)) = dim(Supp(M)) - 1` (tag 0B52), but only
the inequality `dim(Supp(M/f₁M)) + 1 ≤ dim(Supp(M))` is needed, and that holds over any
commutative ring for a nonzerodivisor `f₁` on a finite module.

The source writes the inequality as `dim(Supp(M)) ≥ depth(M)`; it is stated here as `≤` with
the smaller quantity on the left, as Mathlib does.

## References

* [StackProject 00LK](https://stacks.math.columbia.edu/tag/00LK)

## Tags

depth, dimension of support, regular sequence
-/

namespace Module

/-- **Depth is at most the dimension of the support.** If `M` is a finite `R`-module and `I` is
an ideal of `R` with `I • M ≠ M`, then `depth_I(M) ≤ dim(Supp(M))`. For `R` Noetherian local,
`I` the maximal ideal and `M` nonzero, this is `depth(M) ≤ dim(Supp(M))`. -/
@[stacks 00LK, ega "0 16.4.5" "(16.4.5.1)"]
public theorem depth_le_supportDim (R : Type*) [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    (depth R I M : WithBot ℕ∞) ≤ supportDim R M := Stacks.Depth.SupportDimBound.solution R I M hI

/-- **Depth is at most the Krull dimension**: for a local ring `R`, the `𝔪`-depth of `R` is at
most the Krull dimension of `R`. This is `depth_le_supportDim` read at `I = 𝔪` and `M = R`: the
hypothesis `I • M ≠ M` becomes `𝔪 ≠ ⊤`, and `dim Supp(R) = dim R` is
`supportDim_self_eq_ringKrullDim`. Like `depth_le_supportDim` it needs no Noetherian
hypothesis. -/
@[ega "IV 5.7.3" "F = O_X"]
public theorem depth_le_ringKrullDim (R : Type*) [CommRing R] [IsLocalRing R] :
    (depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← supportDim_self_eq_ringKrullDim]
  refine depth_le_supportDim R _ R ?_
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top

end Module

/-!
# Depth along an ideal is finite over a Noetherian ring

Proof of `Module.depth_lt_top` (Stacks 0AUJ): for `R` a Noetherian ring, `I ⊆ R` an ideal and
`M` a finite `R`-module with `I • M ≠ M`, the `I`-depth of `M` is finite.

Since `M/IM ≠ 0` its support is nonempty, and `Supp(M/IM) = Supp(M) ∩ Z(I)`, so there is a
prime `𝔭 ⊇ I` with `𝔭 ∈ Supp(M)`. An `M`-regular sequence `f₁, …, f_r` in `I` then lies in `𝔭`
and cuts a strictly decreasing chain of primes of `Supp(M)` out of `𝔭`: each `fᵢ` is a
nonzerodivisor on `M/(f₁, …, f_{i-1})M`, hence lies in no minimal prime of that module's
annihilator, so a prime of `Supp(M/(f₁, …, f_i)M)` always has a prime of
`Supp(M/(f₁, …, f_{i-1})M)` strictly below it. Consequently `r ≤ height 𝔭`, and
`height 𝔭 < ∞` by Krull's height theorem. As `depth_I(M)` is the supremum of these `r`, it is
finite.

## Main results

* `Stacks.Depth.Finiteness.solution`: `depth_I(M) < ∞` for a finite module `M` over a Noetherian
  ring with `I • M ≠ M`.

## Implementation notes

The chain construction is isolated as
`exists_mem_support_length_add_height_le_of_isWeaklyRegular`: for a weakly `M`-regular sequence
`f₁, …, f_r` contained in a prime `𝔭` of `Supp(M)` there is `𝔮 ∈ Supp(M)` with
`r + height 𝔮 ≤ height 𝔭`. It is the height analogue of Mathlib's
`Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`, iterated over the sequence and
with the chains kept below the fixed prime `𝔭`; that is what makes the bound finite, since
`dim Supp(M)` need not be (a Noetherian ring can have infinite Krull dimension, while every
prime of it has finite height). Neither `R` Noetherian nor `M ≠ 0` is needed for it.

The source's proof localises at `𝔭` and concludes
`depth_I(M) ≤ depth_{I_𝔭}(M_𝔭) ≤ dim Supp(M_𝔭) ≤ dim R_𝔭 = height 𝔭 < ∞`, using that
localisation is flat to carry an `M`-regular sequence in `I` to an `M_𝔭`-regular sequence in
`I_𝔭` and then tag 00LK over `R_𝔭`. The chain that the composite of those inequalities produces
is exactly the one built here directly in `R`: a chain in `Supp(M_𝔭)` is a chain of primes of
`Supp(M)` contained in `𝔭`. Building it in `R` avoids localising the module, the ideal and the
sequence, and needs no flatness; the mathematics is the source's, with `height 𝔭 < ∞`
(`Ideal.finiteHeight_of_isNoetherianRing`, Krull's height theorem) in place of
`dim R_𝔭 < ∞`.

## References

* [StackProject 0AUJ](https://stacks.math.columbia.edu/tag/0AUJ)
-/

@[expose] public section

namespace Stacks.Depth.Finiteness

open RingTheory Sequence PrimeSpectrum

/-- A weakly `M`-regular sequence `f₁, …, f_r` all of whose terms lie in a prime `𝔭` of the
support of a finite module `M` cuts a strictly decreasing chain of `r` primes of `Supp(M)` out
of `𝔭`: there is `𝔮 ∈ Supp(M)` with `r + height 𝔮 ≤ height 𝔭`. In particular `r ≤ height 𝔭`.

This is the height analogue of `Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`,
iterated over the sequence: the successive quotients `M/(f₁, …, f_i)M` all have `𝔭` in their
support, and a prime of `Supp(M/(f₁, …, f_i)M)` contains `fᵢ`, which is a nonzerodivisor on
`M/(f₁, …, f_{i-1})M` and hence lies in no minimal prime of the annihilator of that module. -/
private theorem exists_mem_support_length_add_height_le_of_isWeaklyRegular {R : Type*}
    [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (rs : List R)
    (reg : IsWeaklyRegular M rs) (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hrs : ∀ r ∈ rs, r ∈ p.asIdeal) :
    ∃ q ∈ Module.support R M, (rs.length : ℕ∞) + q.asIdeal.height ≤ p.asIdeal.height := by
  induction rs generalizing M with
  | nil => exact ⟨p, hp, by simp⟩
  | cons x rs' ih =>
      obtain ⟨hx, hrs'⟩ := (isWeaklyRegular_cons_iff M x rs').mp reg
      have hxp : x ∈ p.asIdeal := hrs x List.mem_cons_self
      -- `𝔭` is in the support of `M/xM`, as it contains `x` and lies in `Supp(M)`.
      have hp' : p ∈ Module.support R (QuotSMulTop x M) := by
        rw [Module.support_quotSMulTop]
        exact ⟨hp, by simpa using hxp⟩
      obtain ⟨q, hq, hle⟩ := ih (M := QuotSMulTop x M) hrs' hp'
        fun r hr => hrs r (List.mem_cons_of_mem _ hr)
      rw [Module.support_quotSMulTop] at hq
      obtain ⟨hqM, hxq'⟩ := hq
      have hxq : x ∈ q.asIdeal := by simpa using hxq'
      -- `𝔮` contains `x`, so it is not a minimal prime of the annihilator of `M`.
      obtain ⟨r, hrm, hrq⟩ :=
        Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hqM)
      have hrp : r.IsPrime := hrm.isPrime
      have hlt : r < q.asIdeal :=
        lt_of_le_of_ne hrq fun h => hx.notMem_of_mem_minimalPrimes hrm (by rw [h]; exact hxq)
      refine ⟨⟨r, hrp⟩, Module.mem_support_iff_of_finite.mpr hrm.1.2, ?_⟩
      have hstep : r.height + 1 ≤ q.asIdeal.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have hcast : ((x :: rs').length : ℕ∞) + r.height = (rs'.length : ℕ∞) + (r.height + 1) := by
        rw [List.length_cons]; push_cast; ring
      rw [hcast]
      exact le_trans (add_le_add le_rfl hstep) hle

/-- Over a Noetherian ring `R`, for a finite `R`-module `M` and an ideal `I` with `I • M ≠ M`,
the `I`-depth of `M` is finite: it is bounded by the height of a prime `𝔭 ⊇ I` in `Supp(M)`. -/
public theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth R I M < ⊤ := by
  -- `M/IM` is nonzero, so `Supp(M/IM) = Supp(M) ∩ Z(I)` provides a prime `𝔭 ⊇ I` of `Supp(M)`.
  have hnt : Nontrivial (M ⧸ (I • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr hI
  obtain ⟨p, hp⟩ :=
    Module.nonempty_support_of_nontrivial (R := R) (M := M ⧸ (I • ⊤ : Submodule R M))
  rw [Module.support_quotient I] at hp
  obtain ⟨hpM, hpI⟩ := hp
  have hIp : I ≤ p.asIdeal := fun _ hx => hpI hx
  have hbd : Module.depth R I M ≤ p.asIdeal.height := by
    refine Stacks.Depth.SupportDimBound.depth_le_of_forall_isRegular_length_le hI
      fun rs hmem hreg => ?_
    obtain ⟨q, -, hle⟩ := exists_mem_support_length_add_height_le_of_isWeaklyRegular rs
      hreg.toIsWeaklyRegular p hpM fun r hr => hIp (hmem r hr)
    exact le_trans le_self_add hle
  exact lt_of_le_of_lt hbd Ideal.height_lt_top_of_isPrime

end Stacks.Depth.Finiteness

end

/-!
# Depth along an ideal is finite over a Noetherian ring

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module with `I • M ≠ M`.
Then the `I`-depth of `M` is finite: `depth_I(M) < ∞`. Equivalently, the lengths of the
`M`-regular sequences contained in `I` are bounded.

The reason is local. Since `M/IM ≠ 0` there is a prime `𝔭` in the support of `M/IM`; it
contains `I`, and `(M/IM)_𝔭 ≠ 0` gives `I • M_𝔭 ≠ M_𝔭` because localisation is exact. An
`M`-regular sequence `f₁, …, f_r ∈ I` stays regular after localising at `𝔭`, localisation being
flat and the quotient `M_𝔭/(f₁, …, f_r)M_𝔭` being nonzero because `(f₁, …, f_r) ⊆ I ⊆ 𝔭`; hence
`depth_I(M) ≤ depth_{I_𝔭}(M_𝔭) ≤ dim(Supp(M_𝔭))` by `Module.depth_le_supportDim` (tag 00LK),
and the right-hand side is at most `dim(R_𝔭) = height(𝔭)`, which is finite by Krull's height
theorem. The passage to `R_𝔭` is what makes the argument work: a Noetherian ring can have
infinite Krull dimension, so `dim(Supp(M))` itself need not be finite and the bound of tag
00LK does not by itself give the conclusion.

## Main results

* `Module.depth_lt_top`: `depth_I(M) < ∞` for `R` Noetherian, `M` a finite `R`-module and
  `I` an ideal with `I • M ≠ M`.

## Implementation notes

Faithfulness to [StackProject 0AUJ]:

1. No dead hypothesis. `IsNoetherianRing R` is what the conclusion needs: over the polynomial
   ring `R = k[x₁, x₂, …]` on countably many variables, the cyclic — hence finite — module
   `M = R` and the ideal `I = (x₁, x₂, …)` satisfy `I • M ≠ M`, yet `x₁, x₂, …` is an infinite
   sequence of successive nonzerodivisors and `depth_I(M) = ∞`. `I • (⊤ : Submodule R M) ≠ ⊤`
   is equally load-bearing: `depth_R(M) = ⊤` by the definition of the depth, and it is also
   what supplies the source's hypothesis `M ≠ 0`, which is therefore not assumed separately
   (for `M = 0` one has `I • M = M`). `Module.Finite R M` is the source's hypothesis and is
   used, through the bound `depth_I(M) ≤ dim(Supp(M))` of tag 00LK, which is a statement about
   finite modules.
2. The scalars are the source's. `Module.depth R I M` is formed from sequences in the ideal `I`
   of `R` and quotients `M/(f₁, …, f_i)M` of the `R`-module `M`; the localisation `R_𝔭` of the
   source's proof is a step in that proof and does not appear in the statement.
3. The quantity is pinned, not merely bounded: the subject is the value of `Module.depth R I M`
   (tag 00LI), so the statement is the finiteness of that invariant and not the existence of
   some bound on the lengths of regular sequences in `I`.
4. Not degenerate. For `R = k[x, y]`, `I = (x, y)` and `M = R` all hypotheses hold and
   `depth_I(M) = 2`; for `M = R/(x, y)` they hold with `depth_I(M) = 0`. So the hypotheses are
   satisfiable and the conclusion is not vacuously about an empty class, while the
   counterexample in (1) shows it is not vacuously true either.

Two departures from the source's form, neither weakening it. The source assumes `M` nonzero
alongside `IM ≠ M`; only the latter is assumed here, as it implies the former. The source
writes `depth_I(M) < ∞`, rendered as `< ⊤` in `ℕ∞`, the value group of `Module.depth`; the form
`depth_I(M) ≠ ⊤` is `lt_top_iff_ne_top` away, as it is for Mathlib's sibling pair
`Ideal.height_lt_top` and `Ideal.height_ne_top`.

## References

* [StackProject 0AUJ](https://stacks.math.columbia.edu/tag/0AUJ)

## Tags

depth, regular sequence, Noetherian ring
-/

namespace Module

/-- **Depth along an ideal is finite over a Noetherian ring.** If `R` is Noetherian, `M` is a
finite `R`-module and `I` is an ideal of `R` with `I • M ≠ M`, then `depth_I(M) < ∞`; that is,
the lengths of the `M`-regular sequences contained in `I` are bounded. The hypothesis
`I • M ≠ M` also forces `M ≠ 0`. -/
@[stacks 0AUJ]
public theorem depth_lt_top (R : Type*) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth R I M < ⊤ := Stacks.Depth.Finiteness.solution R I M hI

end Module
