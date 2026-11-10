module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Valuation.ValuationRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A filtered direct limit of valuation rings is a valuation ring

Let `(ι, ≤)` be a directed set and `(G i, f i j)` a directed system of commutative rings
over `ι` in which every `G i` is an integral domain and a valuation ring. Then the
directed colimit `A = colim_i G i` is an integral domain and a valuation ring. This is
Stacks Lemma 10.50.6 (tag 0AS4).

A commutative integral domain is a *valuation ring* when for all `a b` there is `c` with
`a * c = b` or `b * c = a`, that is, divisibility is total. This divisibility criterion
is the content of Stacks tags 00IB and 052K, and agrees with the definition in tag 00I9;
it is Mathlib's `ValuationRing`. The index set being directed means `[Nonempty ι]` and
`[IsDirectedOrder ι]` over a `[Preorder ι]`, and the system is a family `G : ι → Type*`
of commutative rings with ring maps `f i j : G i →+* G j` for `i ≤ j` forming a
`DirectedSystem`. The colimit is `Ring.DirectLimit`, with structure maps
`Ring.DirectLimit.of G f i`.

## Main results

* `valuationRing_directLimit`: the colimit is an integral domain and a valuation ring.

Every element of the colimit comes from some stage, and an element of a stage that dies
in the colimit already dies at a later stage. Both conclusions follow: given `x y` in the
colimit, move both to a common stage `k`, apply the property there, and push the result
forward. For nontriviality and the absence of zero divisors the "dies later" direction is
what is used; for the valuation condition the witness `c` found in `G k` maps to a
witness in the colimit.
-/

@[expose] public section

/-- Two elements of a directed colimit of rings come from a common stage. -/
private theorem exists_common_stage_of
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, CommRing (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => f i j h]
    (x y : Ring.DirectLimit G fun i j h => f i j h) :
    ∃ (k : ι) (a b : G k), x = Ring.DirectLimit.of G (fun i j h => f i j h) k a ∧
      y = Ring.DirectLimit.of G (fun i j h => f i j h) k b := by
  obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨j, b, rfl⟩ := Ring.DirectLimit.exists_of y
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨k, f i k hik a, f j k hjk b, (Ring.DirectLimit.of_f hik a).symm,
    (Ring.DirectLimit.of_f hjk b).symm⟩

/-- A filtered direct limit of valuation rings is a valuation ring: if `(G i, f i j)`
is a directed system of commutative rings over a directed index set in which every
`G i` is an integral domain and a valuation ring, then the colimit
`Ring.DirectLimit G f` is an integral domain and a valuation ring.

The conclusion is phrased as an existential over an `IsDomain` instance together with
`ValuationRing`, because `ValuationRing` is a typeclass whose statement presupposes
`[IsDomain _]`, and Mathlib does not automatically derive `IsDomain` for the colimit. -/
@[stacks 0AS4, ega "IV 5.13.3" "(i), special case"]
theorem valuationRing_directLimit
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, CommRing (G i)] [∀ i, IsDomain (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => f i j h]
    [∀ i, ValuationRing (G i)] :
    ∃ _ : IsDomain (Ring.DirectLimit G fun i j h => f i j h),
      ValuationRing (Ring.DirectLimit G fun i j h => f i j h) := by
  set F := fun i j h => (f i j h : G i → G j) with hF
  set A := Ring.DirectLimit G F with hA
  -- Nontriviality of the colimit: `1 = 0` in the colimit would already hold at a stage.
  have hnt : Nontrivial A := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    refine ⟨1, 0, ?_⟩
    intro h
    have h1 : (Ring.DirectLimit.of G F i) 1 = 0 := by
      rw [map_one]; rw [← h]
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact h1
    rw [map_one] at hj
    exact one_ne_zero hj
  -- No zero divisors: build an IsDomain instance.
  have hnzd : NoZeroDivisors A := by
    refine ⟨?_⟩
    intro x y hxy
    obtain ⟨k, a', b', hxk, hyk⟩ := exists_common_stage_of G f x y
    have hprod : (Ring.DirectLimit.of G F k) (a' * b') = 0 := by
      rw [map_mul, ← hxk, ← hyk]; exact hxy
    obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hprod
    rw [map_mul] at hl
    rcases mul_eq_zero.mp hl with h0 | h0
    · left
      rw [hxk, ← Ring.DirectLimit.of_f hkl a']
      change (Ring.DirectLimit.of G F l) (f k l hkl a') = 0
      rw [h0, map_zero]
    · right
      rw [hyk, ← Ring.DirectLimit.of_f hkl b']
      change (Ring.DirectLimit.of G F l) (f k l hkl b') = 0
      rw [h0, map_zero]
  have := hnt
  have := hnzd
  have hdom : IsDomain A := NoZeroDivisors.to_isDomain A
  refine ⟨hdom, ?_⟩
  -- Valuation ring condition.
  have := hdom
  have : PreValuationRing A := by
    refine ⟨?_⟩
    intro x y
    obtain ⟨k, a', b', hxk, hyk⟩ := exists_common_stage_of G f x y
    obtain ⟨c, hc⟩ := PreValuationRing.cond' (A := G k) a' b'
    refine ⟨(Ring.DirectLimit.of G F k) c, ?_⟩
    rcases hc with hc | hc
    · left
      rw [hxk, hyk, ← map_mul, hc]
    · right
      rw [hxk, hyk, ← map_mul, hc]
  exact ⟨⟩
