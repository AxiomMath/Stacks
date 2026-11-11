module

public import StacksCore.Tactic.StacksAttribute
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
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-!
# Restricting a valuation ring to a subfield

Let `L / K` be an extension of fields and let `B ⊆ L` be a valuation ring, with no
assumption on its fraction field. Then `A = K ∩ B` is a valuation ring
(`Subring.valuationRing_comap`, Stacks tag 052L).

The proof is the divisibility criterion: for `a, b ∈ A` some `c ∈ B` has `a c = b` or
`b c = a` in `B`; when `a ≠ 0` the element `c = b / a` already lies in `K`, hence in `A`.
-/

namespace Subring

variable {K L : Type*} [Field K] [Field L]

/-- Divisibility in `B` between elements of `A = B.comap f`, with the quotient taken in
`B`, descends to divisibility in `A`. -/
private lemma exists_mul_eq_or_of_mul_eq (B : Subring L) (f : K →+* L)
    (a b : B.comap f) (c : B) (hc : f a * c = f b) :
    ∃ c' : B.comap f, a * c' = b ∨ b * c' = a := by
  by_cases ha : (a : K) = 0
  · exact ⟨0, Or.inr (Subtype.ext (by simp [ha]))⟩
  · have hfa : f a ≠ 0 := (map_ne_zero f).mpr ha
    have hcK : f ((b : K) / a) = c := by
      rw [map_div₀]
      exact (eq_div_of_mul_eq hfa (by rw [mul_comm]; exact hc)).symm
    refine ⟨⟨(b : K) / a, ?_⟩, Or.inl (Subtype.ext ?_)⟩
    · rw [Subring.mem_comap, hcK]
      exact c.2
    · simp [mul_div_cancel₀ _ ha]

/-- **Stacks Tag 052L.** Let `f : K → L` be a homomorphism of fields (so `L / K` is a
field extension, `K` identified with its image) and let `B ⊆ L` be a subring which is a
valuation ring. Then `A = K ∩ B`, realized as `B.comap f`, is a valuation ring. No
assumption is made on the fraction field of `B`. -/
@[stacks 052L]
theorem valuationRing_comap (B : Subring L) [ValuationRing B] (f : K →+* L) :
    ValuationRing (B.comap f) where
  cond' a b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (⟨f a, a.2⟩ : B) ⟨f b, b.2⟩
    · exact exists_mul_eq_or_of_mul_eq B f a b c (congrArg Subtype.val hc)
    · exact (exists_mul_eq_or_of_mul_eq B f b a c (congrArg Subtype.val hc)).imp
        fun _ h => h.symm

end Subring

-- ===== merged from StacksDraft.Ch10.Sec50.Tag0AAV =====

/-!
# Restricting a valuation ring along an algebraic extension

Let `L / K` be an algebraic extension of fields and let `B ⊆ L` be a valuation ring with
fraction field `L` that is not a field. Then `A = K ∩ B` is a valuation ring with
fraction field `K`, and `A` is not a field either. This is Stacks tag 0AAV.

## Main definitions

* `intersectionSubring B`: the intersection `A = K ∩ B`, realized as the pullback of `B`
  along `algebraMap K L`.

## Main results

* `mem_intersectionSubring`: `x ∈ A` iff the image of `x` in `L` lies in `B`.
* `intersectionSubring_ne_top`: `A ≠ ⊤`, that is, `A` is not a field.

Suppose `A = ⊤`, so every element of `K` has valuation at most `1` for the valuation `v`
of `B`. Pick `y ∈ L \ B`, so `v y > 1`. Algebraicity gives a nonzero polynomial
`p ∈ K[X]` of degree `d` with `p(y) = 0`. Its leading coefficient `c_d` is a nonzero
element of `K`, so both `v c_d ≤ 1` and `v c_d⁻¹ ≤ 1`, forcing `v c_d = 1` and hence
`v (c_d y^d) = (v y)^d`. Isolating the leading term against the rest of the sum bounds
`(v y)^d ≤ (v y)^{d-1}`, contradicting `v y > 1`.

## Implementation notes

In Mathlib a `ValuationSubring L` is by construction a subring of `L` that is a valuation
ring with fraction field `L`, so writing `B : ValuationSubring L` already encodes both
properties, and the type of `A = B.comap (algebraMap K L)` already delivers the first
conclusion (in this case `Frac B = L`; the general Stacks tag 052L, for any valuation
ring `B ⊆ L`, is `Subring.valuationRing_comap`). "Not a field" is `≠ ⊤`, equivalently a nonzero
maximal ideal, equivalently a nontrivial valuation. What remains, and what genuinely
consumes the algebraicity hypothesis, is that `A ≠ ⊤`: over a transcendental extension
the restricted valuation can be trivial.

The inclusion `K ↪ L` is `algebraMap K L`, injective because `K` is a field, and
algebraicity is `Algebra.IsAlgebraic K L`.
-/

@[expose] public section

/-- The intersection `A = K ∩ B`, realized as the pullback of the valuation subring
`B` of `L` along the inclusion `K → L`. As a `ValuationSubring K` it is a valuation
ring of `K` with fraction field `K`. -/
noncomputable def intersectionSubring
    {K L : Type*} [Field K] [Field L] [Algebra K L] (B : ValuationSubring L) :
    ValuationSubring K :=
  B.comap (algebraMap K L)

/-- Membership in `A = K ∩ B`: an `x : K` lies in `intersectionSubring B` exactly
when its image in `L` lies in `B`. -/
theorem mem_intersectionSubring
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) (x : K) :
    x ∈ intersectionSubring B ↔ algebraMap K L x ∈ B :=
  ValuationSubring.mem_comap

/-- **Stacks Tag 0AAV.** Let `L / K` be an algebraic extension of fields and let
`B` be a valuation subring of `L` (so `B` is a valuation ring with `Frac B = L`)
which is not a field (`B ≠ ⊤`). Then `A = K ∩ B = B.comap (algebraMap K L)` is a
valuation subring of `K` (so a valuation ring with fraction field `K`, by its type)
which is not a field (`A ≠ ⊤`). -/
@[stacks 0AAV]
theorem intersectionSubring_ne_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : Algebra.IsAlgebraic K L)
    (B : ValuationSubring L) (hB : B ≠ ⊤) :
    intersectionSubring B ≠ (⊤ : ValuationSubring K) := by
  intro hAtop
  have hvle : ∀ c : K, B.valuation (algebraMap K L c) ≤ 1 := fun c => by
    rw [B.valuation_le_one_iff, ← mem_intersectionSubring, hAtop]
    trivial
  obtain ⟨y, hyB⟩ : ∃ y : L, y ∉ B := by
    by_contra! hc
    exact hB (by ext x; simp [hc x])
  set v := B.valuation
  have hvy : 1 < v y := not_le.mp ((B.valuation_le_one_iff y).not.mpr hyB)
  obtain ⟨p, hp0, hpy⟩ := halg.isAlgebraic y
  set d := p.natDegree
  have hd1 : 0 < d := Polynomial.natDegree_pos_of_aeval_root hp0 hpy
    fun _ h => (map_eq_zero _).mp h
  have hvlead : v (algebraMap K L (p.coeff d)) = 1 := by
    have hne : algebraMap K L (p.coeff d) ≠ 0 :=
      (map_ne_zero _).mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)
    refine le_antisymm (hvle _) ((v.one_le_val_iff hne).mpr ?_)
    rw [← map_inv₀]
    exact hvle _
  have hsum : ∑ i ∈ Finset.range (d + 1), algebraMap K L (p.coeff i) * y ^ i = 0 := by
    rw [← hpy, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  rw [Finset.sum_range_succ, add_eq_zero_iff_eq_neg'] at hsum
  have hbound :
      v (∑ i ∈ Finset.range d, algebraMap K L (p.coeff i) * y ^ i) ≤ v y ^ (d - 1) := by
    refine Valuation.map_sum_le _ fun i hi => ?_
    rw [map_mul, map_pow]
    calc _ ≤ 1 * v y ^ i := mul_le_mul_left (hvle _) _
      _ ≤ v y ^ (d - 1) := by
        rw [one_mul]
        exact (pow_le_pow_iff_right₀ hvy).mpr (by grind)
  have hfinal : v y ^ d ≤ v y ^ (d - 1) := by
    rwa [← one_mul (v y ^ d), ← hvlead, ← map_pow, ← map_mul, hsum, Valuation.map_neg]
  exact absurd hfinal (not_le.mpr ((pow_lt_pow_iff_right₀ hvy).mpr (by omega)))
