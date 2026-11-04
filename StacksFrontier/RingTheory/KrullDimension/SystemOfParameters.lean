module

public import Mathlib.RingTheory.Regular.RegularSequence
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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

@[expose] public section

/-!
# Dimension of the quotient by part of a system of parameters

Proof of `ringKrullDim_add_length_eq_ringKrullDim_of_radical_ofList_append_eq_maximalIdeal`: if
`x₁, …, x_d` generate an ideal of definition of a Noetherian local ring `(R, m)` and `d ≤ dim R`,
then killing a part `l` of the sequence drops the dimension by exactly `|l|`, that is
`dim R/(l) + |l| = dim R`.

Both inequalities come from Krull's height theorem, and neither needs induction on `d`.

The heart of the matter is that a Noetherian local ring has no ideal of definition with fewer
than `dim R` generators: `dim R = ht(m) = ht(I) ≤ spanFinrank I`, the outer equality because `m`
is the radical of `I` and the height of an ideal depends only on its minimal primes, and the
inequality being Krull's height theorem.

Granting that, both halves are short. For `dim R ≤ dim R/(l) + |l|` no hypothesis on `l` is
needed beyond `(l) ≤ m`: it is `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank` together
with `spanFinrank (l) ≤ |l|`. For the reverse inequality, write `S = R/(l)`. The images of `l'`
generate an ideal of definition of `S`, because taking radicals commutes with the image of an
ideal containing the kernel of a surjection and the image of a maximal ideal containing that
kernel is again maximal; so `dim S ≤ spanFinrank (l') ≤ |l'|` and
`dim S + |l| ≤ |l'| + |l| ≤ dim R` by hypothesis.

## Main results

* `Stacks.KrullDimension.SystemOfParameters.solution`: the quotient of a Noetherian local ring by
  part of a system of parameters has the dimension predicted by counting the parameters killed.

## Implementation notes

The step `dim R ≤ spanFinrank I` for an ideal of definition `I`, isolated below as
`ringKrullDim_le_spanFinrank_of_radical_eq_maximalIdeal`, is the half of [StackProject 00KQ]
item (3) that the argument uses; it is proved here from Mathlib's `Ideal.height_le_spanFinrank`
rather than quoted from that tag, so this file does not depend on it. Mathlib has that step only
for `I = m` (`ringKrullDim_le_spanFinrank_maximalIdeal`).

## References

* [StackProject 02IE](https://stacks.math.columbia.edu/tag/02IE)
-/

namespace Stacks.KrullDimension.SystemOfParameters

open IsLocalRing

/-- The height of an ideal depends only on its radical: `ht(√I) = ht(I)`, because `I` and `√I`
have the same minimal primes. -/
public theorem radical_height {R : Type*} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes,
    Ideal.radical_minimalPrimes]

/-- An ideal of definition is a proper ideal. -/
private theorem ne_top_of_radical_eq_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} (h : I.radical = maximalIdeal R) : I ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.le_radical.trans h.le)

/-- **An ideal of definition has at least `dim R` generators.** If the radical of an ideal `I` of
a Noetherian local ring `R` is the maximal ideal, then `dim R ≤ spanFinrank I`. This is the
sharpening of `ringKrullDim_le_spanFinrank_maximalIdeal` from the maximal ideal to an arbitrary
ideal of definition, and one half of [StackProject 00KQ] item (3). -/
@[ega "0 16.2.5" "partial, special case", ega "IV 5.1.6" "lower bound"]
private theorem ringKrullDim_le_spanFinrank_of_radical_eq_maximalIdeal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (h : I.radical = maximalIdeal R) :
    ringKrullDim R ≤ ((I.spanFinrank : ℕ∞) : WithBot ℕ∞) := by
  calc ringKrullDim R = ((maximalIdeal R).height : WithBot ℕ∞) :=
        maximalIdeal_height_eq_ringKrullDim.symm
    _ = ((I.height : ℕ∞) : WithBot ℕ∞) := by rw [← h, radical_height]
    _ ≤ ((I.spanFinrank : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast Ideal.height_le_spanFinrank I (ne_top_of_radical_eq_maximalIdeal h)

/-- **The image of an ideal of definition is an ideal of definition.** If `f : R →+* S` is a
surjection of local rings and `I` is an ideal of definition of `R` containing the kernel of `f`,
then `f(I)` is an ideal of definition of `S`. -/
private theorem radical_map_eq_maximalIdeal_of_ker_le {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
    (h : I.radical = maximalIdeal R) (hk : RingHom.ker f ≤ I) :
    (Ideal.map f I).radical = maximalIdeal S := by
  rw [← Ideal.map_radical_of_surjective hf hk, h]
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.IsMaximal.map_of_surjective_of_ker_le hf (hk.trans (Ideal.le_radical.trans h.le)))

/-- An ideal generated by a list needs no more than the length of the list to generate it. -/
private theorem spanFinrank_ofList_le_length {R : Type*} [CommRing R] (l : List R) :
    (Ideal.ofList l).spanFinrank ≤ l.length := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite l.finite_toSet).trans ?_
  rw [← List.coe_toFinset, Set.ncard_coe_finset]
  exact l.toFinset_card_le

/-- **Dimension of a quotient by part of a system of parameters.** If `l ++ l'` generates an
ideal of definition of the Noetherian local ring `R` and `|l| + |l'| ≤ dim R`, then
`dim R/(l) + |l| = dim R`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (l l' : List R)
    (hdef : (Ideal.ofList (l ++ l')).radical = IsLocalRing.maximalIdeal R)
    (hdim : ((l.length + l'.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R) :
    ringKrullDim (R ⧸ Ideal.ofList l) + l.length =
      ringKrullDim R := by
  have hsub : Ideal.ofList l ≤ Ideal.ofList (l ++ l') := by
    rw [Ideal.ofList_append]; exact le_sup_left
  have hne : Ideal.ofList l ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_radical_eq_maximalIdeal hdef) hsub
  have : Nontrivial (R ⧸ Ideal.ofList l) := Submodule.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ Ideal.ofList l) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine le_antisymm ?_ ?_
  -- `dim R/(l) ≤ |l'|`: the images of `l'` generate an ideal of definition of `R/(l)`.
  · have key : (Ideal.ofList (l'.map (Ideal.Quotient.mk (Ideal.ofList l)))).radical
        = maximalIdeal (R ⧸ Ideal.ofList l) := by
      have h := radical_map_eq_maximalIdeal_of_ker_le (f := Ideal.Quotient.mk (Ideal.ofList l))
        Ideal.Quotient.mk_surjective hdef (Ideal.mk_ker.trans_le hsub)
      rwa [Ideal.ofList_append, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
        Ideal.map_ofList] at h
    have hS : ringKrullDim (R ⧸ Ideal.ofList l) ≤ (l'.length : WithBot ℕ∞) := by
      refine (ringKrullDim_le_spanFinrank_of_radical_eq_maximalIdeal key).trans ?_
      exact_mod_cast (spanFinrank_ofList_le_length _).trans_eq (l'.length_map _)
    calc ringKrullDim (R ⧸ Ideal.ofList l) + l.length
        ≤ (l'.length : WithBot ℕ∞) + l.length := by gcongr
      _ = ((l.length + l'.length : ℕ) : WithBot ℕ∞) := by push_cast; ring
      _ ≤ ringKrullDim R := hdim
  -- `dim R ≤ dim R/(l) + spanFinrank (l) ≤ dim R/(l) + |l|`, by Krull's height theorem.
  · refine le_trans (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.ofList l) ?_) ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]; exact le_maximalIdeal hne
    · gcongr
      exact_mod_cast spanFinrank_ofList_le_length l

end Stacks.KrullDimension.SystemOfParameters

/-!
# Dimension of the quotient by part of a system of parameters

Let `(R, m)` be a Noetherian local ring, let `x₁, …, x_d ∈ m` generate an *ideal of definition*
of `R`, that is an ideal whose radical is `m`, and suppose `d = dim R`, so that `x₁, …, x_d` is a
system of parameters. Then killing the first `i` of them drops the dimension by exactly `i`:
`dim R/(x₁, …, x_i) = d - i`. Only the splitting of the sequence into the part that is killed and
the part that survives matters, so the statement below takes two lists `l`, `l'` whose
concatenation generates an ideal of definition and whose total length is at most `dim R`, and
concludes `dim R/(l) + |l| = dim R`.

## Main results

* `ringKrullDim_add_length_eq_ringKrullDim_of_radical_ofList_append_eq_maximalIdeal`:
  the quotient of a Noetherian local ring by part of a system of parameters has the dimension
  predicted by counting the parameters killed.

## Implementation notes

Being an ideal of definition (Tag 07DU) is spelled `I.radical = maximalIdeal R`, as in
[StackProject 00K8] and [StackProject 00KQ], and a sequence of elements is a `List R`
generating `Ideal.ofList`, as in the Mathlib sibling
`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`, whose conclusion this one matches in
shape.

Three points of form. First, the source's `dim R/(x₁, …, x_i) = d - i` is stated additively, as
`ringKrullDim (R ⧸ Ideal.ofList l) + l.length = ringKrullDim R`: subtraction in `WithBot ℕ∞` is
truncated, whereas the additive form is subtraction-free and is how the sibling above and
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` state the same kind of equality.

Second, the source's prefix `x₁, …, x_i` of a single sequence `x₁, …, x_d` is replaced by a pair
of lists `l`, `l'` with `l ++ l'` generating the ideal of definition; the source's statement for
the prefix of length `i` is the case `l = x.take i`, `l' = x.drop i`, since
`x.take i ++ x.drop i = x` and `(x.take i).length = min i x.length`. This is not a weakening: it
is what makes the lemma apply to an arbitrary subsequence, since `Ideal.ofList` depends only on
the set of members of the list, and that is what the source itself uses in its application
[StackProject 02IG], where the element removed from the system of parameters `x, y₂, …, y_d` is
`y₂` rather than a prefix.

Third, the source's `d = dim R` for `d = l.length + l'.length` is weakened to
`l.length + l'.length ≤ ringKrullDim R`, which is equivalent to it: the reverse inequality holds
for the generators of any ideal of definition, since such an ideal has `m` as its only minimal
prime and so `dim R = m.height = (Ideal.ofList (l ++ l')).height` is at most the number of
generators by Krull's height theorem (`Ideal.height_le_spanFinrank`,
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`, and [StackProject 00KQ] for the same
inequality in the source's language). Under these hypotheses neither list repeats an element and
`l.length = (Ideal.ofList l).spanFinrank`, so the variants of the conclusion with
`Submodule.spanFinrank` or `Set.encard` in place of `List.length` follow. The source's hypothesis
`x_i ∈ m` is not assumed below because it is implied: `Ideal.ofList (l ++ l')` is contained in its
own radical, which is `m`.

Faithfulness. (1) Every hypothesis is used. Without `hdef`: in `R = k[[x, y]]/(x y)`, of
dimension `1`, the lists `l = [x]` and `l' = []` satisfy `hdim`, and the conclusion fails, as
`dim R/(x) + 1 = dim k[[y]] + 1 = 2 ≠ 1`; there `(x)` is prime and not maximal, so it is not an
ideal of definition. Without `hdim`: in `R = k[[x, y]]` the lists `l = [x, x]` and `l' = [y]`
satisfy `hdef`, and the conclusion fails, as `dim R/(x) + 2 = 3 ≠ 2`. `IsLocalRing R` is what
gives `m` and hence the notion of an ideal of definition, and `IsNoetherianRing R` is what makes
`dim R` finite and Krull's height theorem available. (2) The base is the source's: the elements
are elements of `R`, the ideal of definition is an ideal of `R`, and the two dimensions are those
of a quotient of `R` and of `R` itself, with no localization intervening. (3) The source names no
canonical map; what has to be pinned is the ideal killed, and it is pinned as `Ideal.ofList l`
for the given list rather than existentially. (4) The instantiation is not degenerate:
`R = k[[x, y]]`, `l = [x]`, `l' = [y]` satisfies both hypotheses (`(x, y).radical = m` and
`1 + 1 ≤ 2 = dim R`) and the conclusion reads `dim k[[y]] + 1 = 2`.

## References

* [StackProject 02IE](https://stacks.math.columbia.edu/tag/02IE)
-/

/-- **Dimension of a quotient by part of a system of parameters.** Let `(R, m)` be a Noetherian
local ring and let `x₁, …, x_d ∈ m` generate an ideal of definition of `R`, with
`d ≤ dim R` — equivalently, `x₁, …, x_d` is a system of parameters. Then killing any part
`l` of the sequence drops the dimension by exactly the number of elements killed:
`dim R/(l) + |l| = dim R`. Taking `l` to be the prefix `x₁, …, x_i` gives
`dim R/(x₁, …, x_i) = d - i`. -/
@[stacks 02IE, ega "0 16.2.3.1" "(ii), special case"]
public theorem ringKrullDim_add_length_eq_ringKrullDim_of_radical_ofList_append_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (l l' : List R)
    (hdef : (Ideal.ofList (l ++ l')).radical = IsLocalRing.maximalIdeal R)
    (hdim : ((l.length + l'.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R) :
    ringKrullDim (R ⧸ Ideal.ofList l) + l.length =
      ringKrullDim R := Stacks.KrullDimension.SystemOfParameters.solution l l' hdef hdim
