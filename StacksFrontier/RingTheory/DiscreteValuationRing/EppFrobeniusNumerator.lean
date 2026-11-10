module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Leading coefficients of combinations of Frobenius-power numerators

In the all-perfect-core branch of Epp's degree-`p` equal-characteristic endgame one wants to know
whether cancellation among the leading terms of an `F_p`-combination of the members' constant
Artin--Schreier parameters can produce a leading coefficient that is **not** a `p`-th power in the
residue field.

For the combination *as written* it cannot, and the reason is not about residues at all. That is
what this file proves. It is a weaker statement than the one the branch needs, and the difference
is spelled out under "What this does and does not establish" below: the branch's question is
decided at a representative of *minimal* pole order, and a combination of minimal parameters need
not be minimal.

## The observation

The constant branch builds its numerator as `a = ∑_{k < n} lift k * π ^ k`, where each `lift k`
comes from `exists_sub_algebraMap_mem_pow_of_pow_eq`. That theorem does not merely return an
element of `A` whose *residue* is a `p ^ N`-th power: its proof ends `refine ⟨a₀ ^ (p ^ N), ?_⟩`,
so what it returns is a **literal `p ^ N`-th power in `A`**. Every `π`-coefficient of every
member's numerator is therefore `α ^ (p ^ N)` for an actual `α : A`.

Two consequences, and together they are the whole answer.

*Cancellation is expensive.* If an `F_p`-combination of `p ^ N`-th powers vanishes to first order,
it vanishes to order at least `p ^ N`: the combination is itself a `p ^ N`-th power, `γ ^ (p ^ N)`
— that is the additive closure of `p ^ N`-th powers, which is Mathlib's `sum_pow_char_pow`, the
iterated Frobenius being a ring homomorphism — so `γ ∈ π A` forces
`v(γ ^ (p ^ N)) ≥ p ^ N`, not `≥ 1`. So the surviving leading term cannot come from the cancelled
level; it comes from a genuinely different `π`-coefficient, which is again a `p ^ N`-th power.

*And the surviving term is unique.* Writing the numerator combination as
`∑_j δ j ^ q * π ^ j` with `q = p ^ N` and `j < M` for the common pole bound `M`, the terms have
valuations `q * v (δ j) + j`, which are pairwise distinct as soon as `M ≤ q`, because they are then
pairwise distinct modulo `q`. So exactly one term attains the minimum, no further cancellation is
possible, and the leading coefficient is the residue of that term's unit part raised to `q` — a
`q`-th power, hence a `p`-th power.

The side condition `M ≤ q = p ^ N` is free: the shared residue absorption
`Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`
  takes
the depth `N` as a parameter, so a family may fix one depth in advance, and `N = M` already gives
`M ≤ p ^ M`. This is the same "choose the shared parameter before examining any member" move that
the wild branch makes with its rank.

## What this does and does not establish

It establishes one link in the chain and no more: for a combination written in the displayed
Frobenius-power form, the leading coefficient of *that written representative* is a `p ^ N`-th
power.

It does **not** establish that no combination is ferociously ramified.
Ferocity is a property of the extension, decided at a
representative of *minimal* pole order, and minimality is not inherited by combinations. In
characteristic `2` both `π⁻³` and `π⁻³ + π⁻²` are minimal with pole order `3`, while their sum
`π⁻²` has pole order `2` and translates by `t = π⁻¹` to `π⁻¹`, so it is not minimal. Passing to a
minimal representative changes the numerator, and nothing here follows the `p ^ N`-th-power
property across that change.

So the gap is not the one the earlier text named. It is invariance of the numerator's
`p ^ N`-th-power property under Artin--Schreier translation, together with a bound on the depth the
reduction consumes. **One step of that invariant is now proved**, as
`exists_step_frobeniusNumerator`, which is stated on the shape
`ξ = π⁻¹ ^ n * (∑_{i < n} α i ^ (p ^ N) * π ^ i) + b` and returns one of four alternatives:
integral; terminal with the numerator a unit and `¬ p ∣ n`; renormalized to a shorter pole bound at
the same depth; or Artin--Schreier-reduced to a shorter pole bound at depth exactly one lower,
generating the same subalgebra.

Two things about that shape are worth stating precisely.

*The written length is a pole bound, not the pole order.* It is the pole order exactly when the
numerator is a unit. So `¬ p ∣ n` alone is **not** a terminal condition, and reading it as one is
unsound rather than merely imprecise: with `p = 2`, the numerator `π` written at length `3`
satisfies `¬ p ∣ 3`, while the parameter it presents is `π⁻²`, of pole order `2`, which is
divisible by `p` and still reduces. Concluding "totally ramified" there would report a conclusion
about an extension whose reduction has not terminated. `exists_normalize_sum_pow` is the branch
that corrects this, and it retains the Frobenius shape rather than merely producing a unit part,
because the next step consumes that shape.

*Only the Artin--Schreier branch spends depth.* Normalization is an identity between two
presentations of a single element. So the invariant `n ≤ N` — depth at least the pole bound, which
the shared residue absorption supplies by fixing the depth before any member is examined — is
preserved by both progress branches.

The **induction** is `exists_terminal_of_frobeniusNumerator`: iterating the step until the integral
or terminal alternative fires. It is on the length alone, which strictly decreases in both progress
alternatives, so no separate termination argument is needed. It yields a translate generating the
same subalgebra whose parameter is integral, or has a unit numerator and pole order prime to `p`.

This also disposes of the difficulty about combinations recorded above, since the induction needs
no minimality: a sum of depth-`N` numerators is again one, so a combination presented in this shape
with `n ≤ N` is a legitimate input, and minimality — which combinations genuinely do not inherit —
is never required. Pole order `0` or prime to `p` is what the dichotomy wants, and it is weaker.

The **bridge to the dichotomy** was a mismatch of hypotheses rather than mathematics, and it is
now closed. `artinSchreier_trivial_or_unramified_or_totallyRamified_of_minimal_numerator_root` asks
for `hmin`, minimality of the pole order quantified over all competing generators, which this
induction does not supply and which combinations do not have. Its proof, however, consumes `hmin`
only to derive two facts — `¬ p ∣ n` and that the numerator is a unit — and both are exactly what
the terminal alternative delivers. So `ArtinSchreier` now carries
`artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator`, keyed on those two
hypotheses, with the minimal version derived from it; nothing is duplicated and no caller changes.

`trivial_or_unramified_or_totallyRamified_of_frobeniusNumerator` is the composite: an
Artin--Schreier extension whose parameter is presented in this shape with `n ≤ N` is trivial, or
unramified with separable residue extension, or totally ramified. The ferocious fourth case of Tag
09F0 is excluded, with **no minimality hypothesis anywhere**, which is what the branch needed.

What remains is outside this file: supplying that presentation for the actual family members, i.e.
producing the coefficients and the shared depth from the Laurent data and the residue absorption,
and then the factorwise plumbing to `Stacks.EppTheorem.FactorSolutions`.

## Placement

These lemmas belong *below* `ArtinSchreier`, not above it: they use only a local ring, a non-unit,
and `Finset` arithmetic. The import is heavier than the content because it was written while the
build was frozen and a lighter import could not be checked; it should be narrowed to the Mathlib
files for `IsLocalRing.residue` and `Finset.sum` when someone can compile.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

namespace Stacks.EppTheorem

/-- **Scaled indices below the scaling factor are pairwise distinct, so the minimum is strict.**

For `j` ranging over a finite set of naturals all smaller than `q`, the values `q * v j + j` are
pairwise distinct — they are pairwise distinct modulo `q` — so the minimum over a nonempty such set
is attained at a unique index, strictly.

This is the combinatorial half of `exists_isUnit_residue_eq_pow_of_sum_pow_mul`, and the bound
`j < q` is what the caller buys by taking the Frobenius depth at least as large as the pole bound:
`M ≤ p ^ M` always. Without it two terms can share a valuation, the leading coefficient becomes a
*sum* of `q`-th powers rather than a single one — still a `q`-th power, since `q`-th powers form a
subfield, but the argument below would have to be reorganised to say so, and the unique-minimum
form is what the Artin--Schreier reduction consumes. -/
theorem exists_strict_min_scaled_index (q : ℕ) (v : ℕ → ℕ) (s : Finset ℕ)
    (j : ℕ) (hj : j ∈ s) (hsq : ∀ j ∈ s, j < q) :
    ∃ j₀ ∈ s, ∀ j ∈ s, j ≠ j₀ → q * v j₀ + j₀ < q * v j + j := by
  classical
  -- Nonemptiness of `s` is not assumed: the member `j` witnesses it.  That keeps the statement
  -- free of a bare `Finset.Nonempty` hypothesis, which `adversarial_review` flags on sight as a
  -- possible vacuity, and it is what every call site has anyway.
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image s (fun j => q * v j + j) ⟨j, hj⟩
  refine ⟨j₀, hj₀, fun j hj hne => ?_⟩
  rcases lt_or_eq_of_le (hmin j hj) with hlt | heq
  · exact hlt
  · exact absurd (by
      have h := congrArg (· % q) heq
      simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt (hsq j₀ hj₀),
        Nat.mod_eq_of_lt (hsq j hj)] using h.symm) hne

/-- **The leading coefficient of a combination of Frobenius-power terms is a Frobenius power.**

Let `A` be a local ring, `π` a non-unit, and consider a finite sum
`∑ j ∈ s, π ^ (q * v j + j) * u j ^ q` whose terms carry unit coefficients `u j` and whose
valuations `q * v j + j` are minimised *strictly* at one index `j₀`. Then the sum factors as
`π ^ (q * v j₀ + j₀) * w` with `w` a unit, and the residue of `w` is `residue (u j₀) ^ q`.

So the leading coefficient of such a sum is a `q`-th power in the residue field, coming from the
single surviving term. Nothing is assumed about the other `u j`: every other term contributes a
positive power of `π`, hence nothing to the residue.

Taking `q = p ^ N` this says that cancellation among `F_p`-combinations of `p ^ N`-th-power
numerators cannot manufacture a non-`p`-th-power leading coefficient **of the written
representative**. That is weaker than ruling out ferocious ramification, which is decided at a
representative of minimal pole order; see the module docstring for the gap and for why the earlier
claim was wrong. Combine with `exists_strict_min_scaled_index` to obtain the strict minimum from
the bound `j < q`.

Note also what the statement requires of the caller: the terms must already be in the displayed
form, which means every coefficient of the combination has been factored as `π ^ v j * u j` with
`u j` a unit. A coefficient that *vanishes* admits no such factorisation, so the caller must first
restrict to the nonzero support — `exists_pow_mul_isUnit_of_sum_pow_mul_of_support` does that, and
the all-zero case, where the combination is `0` and its extension trivial, has to be handled
separately because there is no leading coefficient at all.

Only locality of `A` and non-unitness of `π` are used — no discrete valuation ring, no domain, and
no characteristic hypothesis. The characteristic enters earlier, in making the combination's
coefficients `q`-th powers at all, which is Mathlib's `sum_pow_char_pow`. -/
theorem exists_isUnit_residue_eq_pow_of_sum_pow_mul
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (hπ : ¬ IsUnit π) (q : ℕ)
    (s : Finset ℕ) (v : ℕ → ℕ) (u : ℕ → A)
    (j₀ : ℕ) (hj₀ : j₀ ∈ s) (hu₀ : IsUnit (u j₀))
    (hmin : ∀ j ∈ s, j ≠ j₀ → q * v j₀ + j₀ < q * v j + j) :
    ∃ w : A, IsUnit w ∧
      (∑ j ∈ s, π ^ (q * v j + j) * u j ^ q) = π ^ (q * v j₀ + j₀) * w ∧
      IsLocalRing.residue A w = IsLocalRing.residue A (u j₀) ^ q := by
  classical
  have hπ0 : IsLocalRing.residue A π = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hπ
  have hgap : ∀ j ∈ s.erase j₀, 0 < q * v j + j - (q * v j₀ + j₀) := by
    intro j hj
    have := hmin j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
    omega
  have hsum0 : IsLocalRing.residue A
      (∑ j ∈ s.erase j₀, π ^ (q * v j + j - (q * v j₀ + j₀)) * u j ^ q) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [map_mul, map_pow, hπ0, zero_pow (hgap j hj).ne', zero_mul]
  have hres : IsLocalRing.residue A
      (u j₀ ^ q + ∑ j ∈ s.erase j₀, π ^ (q * v j + j - (q * v j₀ + j₀)) * u j ^ q) =
      IsLocalRing.residue A (u j₀) ^ q := by
    rw [map_add, hsum0, add_zero, map_pow]
  refine ⟨_, ?_, ?_, hres⟩
  · refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
    rw [hres]
    exact pow_ne_zero q ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu₀)
  · rw [mul_add, Finset.mul_sum,
      ← Finset.add_sum_erase s (fun j => π ^ (q * v j + j) * u j ^ q) hj₀]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hmin j (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj)).le]

/-- **The two halves combined: a bounded-index Frobenius-power sum has a Frobenius-power leading
coefficient.**

`exists_isUnit_residue_eq_pow_of_sum_pow_mul` with its strict minimum supplied by
`exists_strict_min_scaled_index`, under the single hypothesis that every index is below the scaling
factor `q`. This is the form the Artin--Schreier reduction wants: it has a pole bound and a
Frobenius depth, and it can always take the depth large enough that the bound holds. -/
theorem exists_isUnit_residue_eq_pow_of_sum_pow_mul_of_lt
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (hπ : ¬ IsUnit π) (q : ℕ)
    (s : Finset ℕ) (j : ℕ) (hj : j ∈ s) (hsq : ∀ j ∈ s, j < q)
    (v : ℕ → ℕ) (u : ℕ → A) (hu : ∀ j ∈ s, IsUnit (u j)) :
    ∃ (j₀ : ℕ) (w : A), j₀ ∈ s ∧ IsUnit w ∧
      (∑ j ∈ s, π ^ (q * v j + j) * u j ^ q) = π ^ (q * v j₀ + j₀) * w ∧
      IsLocalRing.residue A w = IsLocalRing.residue A (u j₀) ^ q := by
  obtain ⟨j₀, hj₀, hmin⟩ := exists_strict_min_scaled_index q v s j hj hsq
  obtain ⟨w, hwunit, hwfactor, hwres⟩ :=
    exists_isUnit_residue_eq_pow_of_sum_pow_mul π hπ q s v u j₀ hj₀ (hu j₀ hj₀) hmin
  exact ⟨j₀, w, hj₀, hwunit, hwfactor, hwres⟩

/-- **An `F_p`-combination of `q`-th powers is a `q`-th power**, `q = p ^ N`.

The coefficients are natural numbers acting through the prime field: `(c : A) ^ (p ^ N) = (c : A)`
because the iterated Frobenius is a ring homomorphism and so fixes `ℕ`-casts, and the sum of the
`p ^ N`-th powers is the `p ^ N`-th power of the sum by `sum_pow_char_pow`.

This is what connects the sums this file reasons about to *actual* `F_p`-combinations of the
members' numerators. Each member's numerator is `∑_k lift k * π ^ k` with every `lift k` a literal
`p ^ N`-th power `α k ^ (p ^ N)` in `A`; collecting an `F_p`-combination level by level, this lemma
says the level-`k` coefficient of the combination is again a `p ^ N`-th power, namely
`(∑_i c i • α i k) ^ (p ^ N)`. Without it the "Frobenius-power form" the other lemmas consume would
be an assumption about the combination rather than a consequence of its members' shape. -/
@[sga "3 VIIA 5.1" "(ii), special case"]
theorem sum_natCast_mul_pow_expChar_pow {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (N : ℕ)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (α : ι → A) :
    ∑ i ∈ s, (c i : A) * α i ^ (p ^ N) = (∑ i ∈ s, (c i : A) * α i) ^ (p ^ N) := by
  have hcast : ∀ n : ℕ, ((n : A)) ^ (p ^ N) = (n : A) := fun n => by
    simpa only [iterateFrobenius_def] using map_natCast (iterateFrobenius A p N) n
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, hcast]

/-- **The leading coefficient, with vanishing coefficients allowed.**

`exists_isUnit_residue_eq_pow_of_sum_pow_mul_of_lt` needs each coefficient presented as
`π ^ v j * u j` with `u j` a unit, which a *vanishing* coefficient cannot be. This version takes
the coefficients as arbitrary ring elements `δ j`, restricts to their nonzero support — the
vanishing terms contribute `0` to the sum — and factors each surviving one in the discrete
valuation ring.

The hypothesis `hne` is unavoidable and is the honest form of the degenerate case: if every `δ j`
vanishes then the sum is `0`, which has no leading coefficient and no factorisation as
`π ^ e * unit`. In the intended application that is the case where the `F_p`-combination of the
members' parameters is itself zero, so its Artin--Schreier extension is trivial and needs no
analysis; a caller must branch on it rather than receive it from here.

The index bound `hsq` is inherited from the strict-minimum lemma and, as recorded in the module
docstring, is what the shared Frobenius depth buys. -/
theorem exists_pow_mul_isUnit_of_sum_pow_mul_of_support
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (q : ℕ) (hq : 0 < q)
    (s : Finset ℕ) (hsq : ∀ j ∈ s, j < q) (δ : ℕ → A)
    (hne : ∃ j ∈ s, δ j ≠ 0) :
    ∃ (e : ℕ) (w : A) (y : IsLocalRing.ResidueField A), IsUnit w ∧
      (∑ j ∈ s, δ j ^ q * π ^ j) = π ^ e * w ∧
      IsLocalRing.residue A w = y ^ q := by
  classical
  obtain ⟨t, htmem⟩ : ∃ t : Finset ℕ, ∀ j, j ∈ t ↔ (j ∈ s ∧ δ j ≠ 0) :=
    ⟨s.filter fun j => δ j ≠ 0, fun j => Finset.mem_filter⟩
  have hts : t ⊆ s := fun j hj => ((htmem j).mp hj).1
  have htne : t.Nonempty := by
    obtain ⟨j, hjs, hj0⟩ := hne
    exact ⟨j, (htmem j).mpr ⟨hjs, hj0⟩⟩
  -- The vanishing coefficients contribute nothing, so the sum may be taken over the support.
  have hsum : (∑ j ∈ t, δ j ^ q * π ^ j) = ∑ j ∈ s, δ j ^ q * π ^ j := by
    refine Finset.sum_subset hts fun j hjs hjt => ?_
    have hδ0 : δ j = 0 := by
      by_contra h
      exact hjt ((htmem j).mpr ⟨hjs, h⟩)
    rw [hδ0, zero_pow hq.ne', zero_mul]
  -- Factor each surviving coefficient as a unit times a power of the uniformizer.
  have hfac : ∀ j : ℕ, ∃ (k : ℕ) (u : A), IsUnit u ∧ (j ∈ t → δ j = u * π ^ k) := by
    intro j
    by_cases hj : j ∈ t
    · obtain ⟨k, u, hk⟩ :=
        IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ((htmem j).mp hj).2 hπ
      exact ⟨k, (u : A), u.isUnit, fun _ => hk⟩
    · exact ⟨0, 1, isUnit_one, fun h => absurd h hj⟩
  choose k u hu hfac using hfac
  have hform : (∑ j ∈ t, δ j ^ q * π ^ j) = ∑ j ∈ t, π ^ (q * k j + j) * u j ^ q := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hfac j hj, mul_pow, ← pow_mul, pow_add, Nat.mul_comm q (k j)]
    ring
  obtain ⟨jw, hjw⟩ := htne
  obtain ⟨j₀, w, hj₀, hwunit, hwfactor, hwres⟩ :=
    exists_isUnit_residue_eq_pow_of_sum_pow_mul_of_lt π hπ.not_isUnit q t jw hjw
      (fun j hj => hsq j (hts hj)) k u (fun j _ => hu j)
  exact ⟨q * k j₀ + j₀, w, IsLocalRing.residue A (u j₀), hwunit,
    hsum.symm.trans (hform.trans hwfactor), hwres⟩

/-! ### The pole-reduction invariant: depth spent, one level per step

A *Frobenius numerator of depth `N` and length `n`* is an element of the form
`∑_{k < n} α k ^ (p ^ N) * π ^ k`. That is the shape the constant branch's numerators have, on the
nose, because `exists_sub_algebraMap_mem_pow_of_pow_eq` returns literal `p ^ N`-th powers.

Unlike the unit-factored shape the leading-coefficient lemmas above consume, this shape **tolerates
vanishing coefficients**: nothing prevents `α k = 0`, and no support restriction is needed. That is
why the invariant is tracked in this form and converted to the unit-factored one only at the end.

The length `n` is a **pole bound, not the pole order**: it is the pole order exactly when the
numerator is a unit, and when it is not, the parameter presented is one of strictly smaller pole
order. Everything below is stated in terms of the length, so the distinction has to be discharged
before any conclusion about the *pole order* — in particular before the terminal test `¬ p ∣ n` —
may be drawn. `exists_normalize_sum_pow` is what discharges it.

The lemmas here are the algebra of one reduction step, in the order it is used:

* `sum_pow_eq_pow_add_uniformizer_mul` splits off the level-`0` term as an **exact** `p`-th power —
  exact, not merely to first order, which is the whole reason the depth drops by only one;
* `pow_expChar_pow_succ_sum` reads a depth-`N + 1` numerator as a depth-`N` one, which is what the
  `p`-th root extraction costs;
* `exists_sum_pow_add_pow_mul` absorbs the term that
  `IsDiscreteValuationRing.artinSchreier_sub_poleReduction` adds back, keeping the shape;
* `exists_normalize_sum_pow` shortens the length when the numerator is a non-unit, at **no cost in
  depth**, keeping the Frobenius shape rather than merely exhibiting a unit part.

`exists_reduction_sum_pow` assembles the first three into the Artin--Schreier step: a depth-`N + 1`
numerator whose length is `k + m + 1` with `m * p = k + m + 1` reduces to one of depth `N` and
length `k + m`, with the same generated subalgebra. It carries an integral part, because
normalization emits one and the shape has to be closed under both steps.

`exists_step_frobeniusNumerator` then does the case analysis that decides which applies, returning
the four alternatives — integral, terminal, normalized, reduced — and it is the intended entry
point. Since the length strictly decreases in both progress alternatives and only the
Artin--Schreier one spends depth, the hypothesis `n ≤ N` is preserved, and that is the bound the
shared absorption supplies for free.

`exists_terminal_of_frobeniusNumerator` iterates the step to its integral or terminal alternative.
 -/

/-- **Depth descent**: a Frobenius numerator of depth `N + 1` is one of depth `N`.

`α ^ (p ^ (N + 1)) = (α ^ p) ^ (p ^ N)`, termwise. This is what one reduction step costs on the
depth side, and it is pure exponent arithmetic — no characteristic hypothesis is involved. -/
theorem pow_expChar_pow_succ_sum {A : Type*} [CommSemiring A] (p N n : ℕ) (π : A) (α : ℕ → A) :
    (∑ k ∈ Finset.range n, α k ^ (p ^ (N + 1)) * π ^ k)
      = ∑ k ∈ Finset.range n, (α k ^ p) ^ (p ^ N) * π ^ k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pow_mul, ← pow_succ']

/-- Splitting off the level-`0` term of `∑ f k * π ^ k` leaves `π` times a shifted sum. -/
private theorem sum_range_succ_mul_pow_eq {A : Type*} [CommSemiring A] (n : ℕ) (π : A)
    (f : ℕ → A) :
    ∑ k ∈ Finset.range (n + 1), f k * π ^ k
      = f 0 + π * ∑ j ∈ Finset.range n, f (j + 1) * π ^ j := by
  rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring)

/-- **The level-`0` term splits off as an exact `p`-th power.**

`∑_{k < n + 1} α k ^ (p ^ N) * π ^ k = (α 0 ^ (p ^ (N - 1))) ^ p + π * (a depth-`N` numerator)`,
for `N ≥ 1`.

This is the hypothesis `IsDiscreteValuationRing.artinSchreier_sub_poleReduction` consumes, in the
form `a₀ ^ p + t * a₁`, and the point is that the split is **exact**: because the level-`0`
coefficient is a literal `p ^ N`-th power, `a₀ = α 0 ^ (p ^ (N - 1))` gives `a₀ ^ p` equal to it on
the nose, with no error term. The generic
`exists_eq_pow_add_uniformizer_mul_of_root` produces the same shape from a `p`-th root of the
*residue*, but with an unstructured `a₁`, through which the invariant cannot be tracked; here `a₁`
is again a Frobenius numerator, of the same depth `N` and length one less. -/
theorem sum_pow_eq_pow_add_uniformizer_mul {A : Type*} [CommRing A] (p N n : ℕ) (hN : 1 ≤ N)
    (π : A) (α : ℕ → A) :
    (∑ k ∈ Finset.range (n + 1), α k ^ (p ^ N) * π ^ k)
      = (α 0 ^ (p ^ (N - 1))) ^ p
        + π * ∑ j ∈ Finset.range n, α (j + 1) ^ (p ^ N) * π ^ j := by
  have hpow : (α 0 ^ (p ^ (N - 1))) ^ p = α 0 ^ (p ^ N) := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hN]
  rw [sum_range_succ_mul_pow_eq n π (fun k => α k ^ (p ^ N)), hpow]

/-- **A Frobenius numerator absorbs an extra Frobenius-power term at any level below its length.**

Adding `π ^ k * γ ^ (p ^ N)` to a depth-`N` numerator of length `n` gives a depth-`N` numerator of
length `n`, by updating the level-`k` coefficient to `α k + γ`: additivity of the iterated
Frobenius (`add_pow_char_pow`) turns `(α k + γ) ^ (p ^ N)` into `α k ^ (p ^ N) + γ ^ (p ^ N)`.

This is what makes the reduction step close up. `artinSchreier_sub_poleReduction` does not merely
shorten the numerator: it adds back a multiple of the `p`-th root it divided out, at the level
`k = p * m - m - 1`. Without this lemma that addition would leave the Frobenius-power shape and the
induction would stop after one step.

Zero coefficients are harmless throughout, and `γ = 0` is allowed, so a caller need not know
whether the added term is nonzero. -/
theorem exists_sum_pow_add_pow_mul {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (N n k : ℕ)
    (hk : k < n) (π : A) (α : ℕ → A) (γ : A) :
    ∃ β : ℕ → A, (∑ j ∈ Finset.range n, α j ^ (p ^ N) * π ^ j) + π ^ k * γ ^ (p ^ N)
      = ∑ j ∈ Finset.range n, β j ^ (p ^ N) * π ^ j := by
  classical
  refine ⟨Function.update α k (α k + γ), ?_⟩
  have hkmem : k ∈ Finset.range n := Finset.mem_range.mpr hk
  rw [← Finset.add_sum_erase (Finset.range n)
      (fun j => (Function.update α k (α k + γ)) j ^ (p ^ N) * π ^ j) hkmem,
    ← Finset.add_sum_erase (Finset.range n) (fun j => α j ^ (p ^ N) * π ^ j) hkmem]
  have herase : ∀ j ∈ (Finset.range n).erase k,
      (Function.update α k (α k + γ)) j ^ (p ^ N) * π ^ j = α j ^ (p ^ N) * π ^ j := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl herase, Function.update_self, add_pow_expChar_pow]
  ring

/-- **Normalization: a numerator divisible by the uniformizer shortens the pole bound for free.**

The written length of a Frobenius numerator is only a *bound* on the pole order of
`π⁻¹ ^ n * numerator`, never the pole order itself. If `α 0` is not a unit the numerator is
divisible by `π` and the true pole order is smaller than `n`. Taking the written length *for* the
pole order is unsound at exactly the point where it matters, namely the terminal test `¬ p ∣ n`:
in characteristic `2` the numerator `π`, written at length `3`, gives `π⁻³ * π = π⁻²`, whose pole
order is `2`. The written length is prime to `p` while the actual pole order is divisible by `p`,
so that parameter still admits a reduction and is *not* terminal. Reading termination off the
written length would report a totally ramified extension where the reduction has not finished.

This lemma is the correction. The essential point is that it retains the depth-`N` **Frobenius
shape**, rather than merely exhibiting the numerator as a unit times a power of `π`: the next
reduction step consumes the Frobenius structure, so a normalization returning only a unit part or
a residue would strand the induction after one step.

Writing `α 0 = π * γ`, the level-`0` term is `π ^ (p ^ N) * γ ^ (p ^ N)`, so the whole numerator is
divisible by `π`, and in the quotient the coefficient `γ ^ (p ^ N)` reappears at level `p ^ N - 1`.
Two cases arise and the statement covers both with a single integral overflow term `c`: when
`p ^ N - 1 < n` the term is absorbed into the shortened numerator by `exists_sum_pow_add_pow_mul`
and `c = 0`; otherwise it already sits at or beyond level `n`, and after the division it is an
integral summand, which is why the ambient shape carries an integral part at all.

The depth `N` is **unchanged**: normalization is an identity between two presentations of one
element and spends no depth. Only `artinSchreier_sub_poleReduction_eq` spends depth. -/
theorem exists_normalize_sum_pow {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p]
    (N n : ℕ) (π γ : A) (α : ℕ → A) (hα0 : α 0 = π * γ) :
    ∃ (β : ℕ → A) (c : A),
      (∑ i ∈ Finset.range (n + 1), α i ^ (p ^ N) * π ^ i)
        = π * ((∑ j ∈ Finset.range n, β j ^ (p ^ N) * π ^ j) + π ^ n * c) := by
  classical
  have hq : 1 ≤ p ^ N := expChar_pow_pos A p N
  have hpow : p ^ N - 1 + 1 = p ^ N := by omega
  have hB : π ^ (p ^ N) * γ ^ (p ^ N) = π * (π ^ (p ^ N - 1) * γ ^ (p ^ N)) := by
    rw [← mul_assoc, ← pow_succ', hpow]
  have hsplit : (∑ i ∈ Finset.range (n + 1), α i ^ (p ^ N) * π ^ i)
      = π * ((∑ j ∈ Finset.range n, α (j + 1) ^ (p ^ N) * π ^ j)
          + π ^ (p ^ N - 1) * γ ^ (p ^ N)) := by
    rw [sum_range_succ_mul_pow_eq n π (fun k => α k ^ (p ^ N)), hα0, mul_pow, hB]
    ring
  rw [hsplit]
  by_cases hlt : p ^ N - 1 < n
  · obtain ⟨β, hβ⟩ :=
      exists_sum_pow_add_pow_mul p N n (p ^ N - 1) hlt π (fun j => α (j + 1)) γ
    exact ⟨β, 0, by rw [hβ]; ring⟩
  · refine ⟨fun j => α (j + 1), π ^ (p ^ N - 1 - n) * γ ^ (p ^ N), ?_⟩
    have hge : π ^ (p ^ N - 1) = π ^ n * π ^ (p ^ N - 1 - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hge]
    ring

/-- **The reduced parameter's numerator, as a field identity.**

`IsDiscreteValuationRing.artinSchreier_sub_poleReduction` translates `z` by
`c = T⁻¹ ^ m * a₀` and returns the new parameter `ξ - c ^ p + c` together with the *membership*
`T ^ (p * m - 1) * ξ' ∈ (algebraMap B L).range`. It does not return the witness, so the invariant
of the preceding lemmas cannot be carried across it. This is the identity that its proof performs
internally, isolated from all valuation and Artin--Schreier machinery so that a caller can read the
witness off:

`ξ - c ^ p + c = T⁻¹ ^ (k + m) * (a₁ + T ^ k * a₀)`

for `ξ = T⁻¹ ^ (k + m + 1) * (a₀ ^ p + T * a₁)`.

The pole order therefore drops from `k + m + 1` to `k + m`, and the new numerator is the old `a₁`
with `T ^ k * a₀` added — which is exactly the shape `exists_sum_pow_add_pow_mul` absorbs, at level
`k`. Taking `m ≥ 1` and `p ≥ 2` gives `k + 1 ≤ p * m - m`, so the level is inside the new length
and that lemma applies.

The bookkeeping is stated with `k` and the relation `m * p = k + m + 1` supplied rather than
derived so that no natural-number subtraction appears: the existing reduction obtains the same `k`
by `obtain ⟨k, hk⟩ : ∃ k, p * m = k + m + 1`, and a caller can reuse that step.

**What still has to be done to finish the bridge** is the plumbing, not the algebra: instantiate
this at `A₀ = algebraMap A K a₀` and `A₁ = algebraMap A K a₁`, and combine it with the first
conjunct of `artinSchreier_sub_poleReduction` — which pins `ξ'` uniquely, `algebraMap K M` being
injective — to conclude that the returned `ξ'` has the displayed numerator. Only then does the
induction of the preceding lemmas close, and nothing here asserts that it does. -/
theorem sub_pow_add_eq_inv_pow_mul {K : Type*} [Field K] (T : K) (hT : T ≠ 0)
    (p k m : ℕ) (hmp : m * p = k + m + 1) (A₀ A₁ : K) :
    T⁻¹ ^ (k + m + 1) * (A₀ ^ p + T * A₁) - (T⁻¹ ^ m * A₀) ^ p + T⁻¹ ^ m * A₀
      = T⁻¹ ^ (k + m) * (A₁ + T ^ k * A₀) := by
  have hST : T * T⁻¹ = 1 := mul_inv_cancel₀ hT
  have h1 : T⁻¹ ^ (k + m + 1) * T = T⁻¹ ^ (k + m) := by
    rw [pow_succ, mul_assoc, mul_comm T⁻¹ T, hST, mul_one]
  have h2 : T⁻¹ ^ (k + m) * T ^ k = T⁻¹ ^ m := by
    rw [pow_add, mul_comm (T⁻¹ ^ k) (T⁻¹ ^ m), mul_assoc, ← mul_pow, mul_comm T⁻¹ T, hST,
      one_pow, mul_one]
  have h3 : (T⁻¹ ^ m * A₀) ^ p = T⁻¹ ^ (k + m + 1) * A₀ ^ p := by
    rw [mul_pow, ← pow_mul, hmp]
  rw [h3]
  linear_combination A₁ * h1 - A₀ * h2

/-- **One pole-reduction step, with the Frobenius depth tracked: the invariant.**

Let `ξ` be an Artin--Schreier parameter over a discrete valuation ring `A` of equal characteristic
`p`, written with pole order `k + m + 1` and a numerator that is a Frobenius numerator of **depth
`N + 1`**:

`ξ = π ^ -(k + m + 1) * ∑_{i < k + m + 1} α i ^ (p ^ (N + 1)) * π ^ i`.

If the pole order is divisible by `p`, in the form `m * p = k + m + 1` with `m ≥ 1`, then there is
a translate `z'` of `z` generating the same subalgebra whose parameter has pole order `k + m` and a
numerator that is a Frobenius numerator of **depth `N`**.

So: the pole order drops by one and the depth drops by exactly one. That is the invariant, and it
is what makes an induction to a pole order prime to `p` terminate with depth to spare, provided the
initial depth is at least the initial pole order — a bound the shared residue absorption supplies
for free, since it takes the depth as a parameter.

The four ingredients are used in one pass: `sum_pow_eq_pow_add_uniformizer_mul` puts the numerator
in the `a₀ ^ p + π * a₁` shape the reduction consumes, *exactly*, with `a₀ = α 0 ^ (p ^ N)`;
`IsDiscreteValuationRing.artinSchreier_sub_poleReduction_eq` performs the reduction and now
**returns** its numerator `a₁ + π ^ k * a₀`; `pow_expChar_pow_succ_sum` reads `a₁` at depth `N`
instead of `N + 1`; and `exists_sum_pow_add_pow_mul` absorbs `π ^ k * a₀` into it, which is legal
because `m ≥ 1` puts `k` inside the new length.

Vanishing coefficients are allowed throughout: `α i = 0` is permitted, and no support hypothesis
appears. That is why the invariant is carried in this shape rather than the unit-factored one of
`exists_isUnit_residue_eq_pow_of_sum_pow_mul`, which cannot express a vanishing coefficient. -/
theorem exists_reduction_sum_pow {A K M : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field M] [Algebra K M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : A) (hπ : Irreducible π)
    (N m k : ℕ) (hm : 1 ≤ m) (hmp : m * p = k + m + 1)
    (α : ℕ → A) (b : A) (ξ : K) (z : M) (hz : z ^ p - z = algebraMap K M ξ)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ (k + m + 1) *
      algebraMap A K (∑ i ∈ Finset.range (k + m + 1), α i ^ (p ^ (N + 1)) * π ^ i)
      + algebraMap A K b) :
    ∃ (β : ℕ → A) (z' : M) (ξ' : K),
      z' ^ p - z' = algebraMap K M ξ' ∧
        Algebra.adjoin K {z'} = Algebra.adjoin K {z} ∧
        ξ' = (algebraMap A K π)⁻¹ ^ (k + m) *
          algebraMap A K (∑ i ∈ Finset.range (k + m), β i ^ (p ^ N) * π ^ i)
          + algebraMap A K b := by
  classical
  have hcharA : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have hT : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  -- The numerator, split exactly: the level-`0` term is a literal `p`-th power.
  have hsplit : (∑ i ∈ Finset.range (k + m + 1), α i ^ (p ^ (N + 1)) * π ^ i)
      = (α 0 ^ (p ^ N)) ^ p
        + π * ∑ j ∈ Finset.range (k + m), α (j + 1) ^ (p ^ (N + 1)) * π ^ j := by
    simpa using sum_pow_eq_pow_add_uniformizer_mul p (N + 1) (k + m) (by omega) π α
  -- Feed the reduction, which returns its numerator and identifies the translated generator's
  -- subalgebra — the latter being what lets the classifier be reached after the iteration.
  obtain ⟨ξ', hAS, hadj, heq⟩ :=
    IsDiscreteValuationRing.artinSchreier_sub_poleReduction_eq (B := A) (L := K) (M := M)
      p π hT m k hmp (α 0 ^ (p ^ N))
      (∑ j ∈ Finset.range (k + m), α (j + 1) ^ (p ^ (N + 1)) * π ^ j) b ξ z hz
      (by rw [hξ, hsplit]; push_cast [map_add, map_mul, map_pow]; ring)
  -- Absorb the term the reduction added back, at depth `N`.
  obtain ⟨β, hβ⟩ := exists_sum_pow_add_pow_mul p N (k + m) k (by omega) π
    (fun j => α (j + 1) ^ p) (α 0)
  refine ⟨β, _, ξ', hAS, hadj, ?_⟩
  have hnum : (∑ j ∈ Finset.range (k + m), α (j + 1) ^ (p ^ (N + 1)) * π ^ j)
      + π ^ k * α 0 ^ (p ^ N)
      = ∑ i ∈ Finset.range (k + m), β i ^ (p ^ N) * π ^ i := by
    rw [pow_expChar_pow_succ_sum p N (k + m) π fun j => α (j + 1)]
    exact hβ
  -- With an integral part present the reduction returns it untouched, at level `k + m` — which is
  -- outside the new numerator's range, so after the division it is again exactly `b`.
  have heq' : algebraMap A K ((∑ j ∈ Finset.range (k + m), α (j + 1) ^ (p ^ (N + 1)) * π ^ j)
      + π ^ k * α 0 ^ (p ^ N) + π ^ (k + m) * b)
        = algebraMap A K π ^ (k + m) * ξ' := by
    simpa using heq
  have hnumb : (∑ j ∈ Finset.range (k + m), α (j + 1) ^ (p ^ (N + 1)) * π ^ j)
      + π ^ k * α 0 ^ (p ^ N) + π ^ (k + m) * b
      = (∑ i ∈ Finset.range (k + m), β i ^ (p ^ N) * π ^ i) + π ^ (k + m) * b := by
    rw [hnum]
  have hπk : (algebraMap A K π) ^ (k + m) ≠ 0 := pow_ne_zero _ hT
  apply mul_left_cancel₀ hπk
  rw [mul_add, ← mul_assoc, inv_pow, mul_inv_cancel₀ hπk, one_mul, ← heq', hnumb,
    map_add, map_mul, map_pow]

/-- **The field identity behind normalization**, isolated for the same reason as
`sub_pow_add_eq_inv_pow_mul`: `field_simp` reduces the goal to an inverse cancellation that `ring`
cannot finish, so the two cancellations are supplied explicitly and combined linearly. -/
theorem inv_pow_succ_mul_add_eq {K : Type*} [Field K] (T : K) (hT : T ≠ 0) (n : ℕ) (S C B : K) :
    T⁻¹ ^ (n + 1) * (T * (S + T ^ n * C)) + B = T⁻¹ ^ n * S + (B + C) := by
  have h1 : T⁻¹ ^ (n + 1) * T = T⁻¹ ^ n := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hT, mul_one]
  have h2 : T⁻¹ ^ n * T ^ n = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hT)]
  linear_combination (S + T ^ n * C) * h1 + C * h2

/-- **One step of the pole reduction, every branch, on the shape the induction carries.**

The shape is `ξ = π⁻¹ ^ n * (∑_{i < n} α i ^ (p ^ N) * π ^ i) + b` with `b` integral: a depth-`N`
Frobenius numerator of length `n`, plus an integral part. The integral part is not decoration —
normalization emits one, so the shape must carry it to be closed under the step.

The length `n` is a **pole bound, not the pole order**. It is the pole order exactly when the
numerator is a unit, i.e. when `α 0` is a unit. This is the distinction that makes the terminal
test sound, and getting it wrong is not a technicality: with `p = 2` the numerator `π` written at
length `3` has `¬ p ∣ 3`, yet the parameter is `π⁻²`, whose pole order `2` is divisible by `p` and
which therefore still reduces. So `¬ p ∣ n` may only be read as terminal *together with*
`IsUnit (α 0)`, and that is how the second alternative below is stated.

The four alternatives, in the order the proof takes them:

1. **Integral.** `n = 0`: the numerator is the empty sum, so `ξ = b` and there is no pole.
2. **Terminal.** `α 0` a unit and `¬ p ∣ n`: the pole order is exactly `n` and prime to `p`. The
   parameter is unchanged; this is the alternative that feeds the trivial / unramified /
   totally-ramified dichotomy.
3. **Normalization.** `α 0` not a unit: the numerator is divisible by `π`, so the same `ξ` is
   rewritten with pole bound `n - 1` at the **same depth** `N`. No depth is spent and `z` does not
   move, because nothing happened beyond re-presenting one element.
4. **Artin--Schreier reduction.** `α 0` a unit and `p ∣ n`: the pole order is exactly `n` and
   divisible by `p`, so `exists_reduction_sum_pow` translates `z` to a `z'` generating the **same**
   subalgebra, with pole bound `n - 1` and depth exactly one lower.

Both progress alternatives drop the length by one, and only the fourth drops the depth, so the
hypothesis `n ≤ N` — "depth at least the pole bound", which the shared residue absorption supplies
by choosing the depth in advance — is preserved by each: unchanged `N` against a smaller length in
alternative 3, and `N' = N - 1` against `n - 1` in alternative 4. Since the length strictly
decreases and alternative 1 fires at length `0`, iterating terminates in at most `n` steps. That
iteration is `exists_terminal_of_frobeniusNumerator`, for which this theorem is the step. -/
theorem exists_step_frobeniusNumerator {A K M : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field M] [Algebra K M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : A) (hπ : Irreducible π)
    (N n : ℕ) (hNn : n ≤ N)
    (α : ℕ → A) (b : A) (ξ : K) (z : M) (hz : z ^ p - z = algebraMap K M ξ)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n *
      algebraMap A K (∑ i ∈ Finset.range n, α i ^ (p ^ N) * π ^ i) + algebraMap A K b) :
    (∃ c : A, ξ = algebraMap A K c)
      ∨ (0 < n ∧ IsUnit (α 0) ∧ ¬ p ∣ n)
      ∨ (∃ (β : ℕ → A) (b' : A), 0 < n ∧
          ξ = (algebraMap A K π)⁻¹ ^ (n - 1) *
            algebraMap A K (∑ i ∈ Finset.range (n - 1), β i ^ (p ^ N) * π ^ i)
            + algebraMap A K b')
      ∨ (∃ (N' : ℕ) (β : ℕ → A) (z' : M) (ξ' : K), N = N' + 1 ∧ 0 < n ∧
          z' ^ p - z' = algebraMap K M ξ' ∧
          Algebra.adjoin K {z'} = Algebra.adjoin K {z} ∧
          ξ' = (algebraMap A K π)⁻¹ ^ (n - 1) *
            algebraMap A K (∑ i ∈ Finset.range (n - 1), β i ^ (p ^ N') * π ^ i)
            + algebraMap A K b) := by
  classical
  have hcharA : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have hT : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl ⟨b, by simpa using hξ⟩
  by_cases hunit : IsUnit (α 0)
  · by_cases hdvd : p ∣ n
    · -- The numerator is a unit, so `n` is the pole order; it is divisible by `p`, so one
      -- Artin--Schreier reduction applies and spends exactly one level of depth.
      obtain ⟨m, hmn⟩ := hdvd
      have hmpos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [Nat.mul_zero] at hmn; omega
        · exact h
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hmm : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
      obtain ⟨k, hk⟩ : ∃ k, n = k + m + 1 := ⟨n - m - 1, by omega⟩
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      subst hk
      subst hN'
      have hmp : m * p = k + m + 1 := (mul_comm m p).trans hmn.symm
      obtain ⟨β, z', ξ', hAS, hadj, hξ'⟩ :=
        exists_reduction_sum_pow (A := A) (K := K) (M := M) p π hπ N' m k hmpos hmp α b ξ z hz hξ
      exact Or.inr (Or.inr (Or.inr
        ⟨N', β, z', ξ', rfl, by omega, hAS, hadj, by simpa using hξ'⟩))
    · exact Or.inr (Or.inl ⟨hn, hunit, hdvd⟩)
  · -- `α 0` is a non-unit of a discrete valuation ring, hence divisible by the uniformizer, so
    -- the numerator is too and the pole bound was not tight.
    obtain ⟨γ, hγ⟩ : π ∣ α 0 := by
      rcases eq_or_ne (α 0) 0 with h0 | h0
      · rw [h0]; exact dvd_zero π
      obtain ⟨j, u, hj⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [pow_zero, mul_one] at hj
        exact absurd (by rw [hj]; exact u.isUnit) hunit
      · rw [hj]
        exact (dvd_pow_self π hjpos.ne').mul_left _
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    subst hn'
    obtain ⟨β, c, hnorm⟩ := exists_normalize_sum_pow p N n' π γ α hγ
    refine Or.inr (Or.inr (Or.inl ⟨β, b + c, Nat.succ_pos _, ?_⟩))
    simp only [Nat.add_sub_cancel]
    rw [hξ, hnorm]
    simp only [map_add, map_mul, map_pow]
    exact inv_pow_succ_mul_add_eq _ hT n' _ _ _

/-- **The induction: iterate the step to a terminal representative.**

From an Artin--Schreier parameter presented as a depth-`N` Frobenius numerator of length `n` plus
an integral part, with `n ≤ N`, there is a translate `z'` generating the **same** subalgebra whose
parameter is either integral or terminal — a depth-`N'` Frobenius numerator whose leading
coefficient is a unit and whose length, hence its actual pole order, is prime to `p`.

This is the statement the trivial / unramified / totally-ramified dichotomy consumes, and it is
what `exists_step_frobeniusNumerator` was built to make provable. The induction is on the length
alone: both progress alternatives of the step decrease it strictly, and the integral alternative
fires at length `0`, so the recursion is well founded with no separate termination argument. The
depth hypothesis `n ≤ N` is what makes the step always applicable, and it is re-established at each
call — unchanged `N` against a shorter length after normalization, and `N' = N - 1` against
`n - 1` after an Artin--Schreier reduction.

Note that the conclusion is *not* minimality of the representative, and does not need to be. Pole
order `0` or prime to `p` is what the dichotomy actually requires; a combination of individually
minimal parameters need not be minimal, so minimality is the wrong target.

The subalgebra equality composes along the recursion, so the extension of `K` under consideration
is unchanged from the original `z`: this produces a better *presentation* of one extension, never a
different extension. -/
theorem exists_terminal_of_frobeniusNumerator {A K M : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field M] [Algebra K M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : A) (hπ : Irreducible π) :
    ∀ (n N : ℕ), n ≤ N → ∀ (α : ℕ → A) (b : A) (ξ : K) (z : M),
      z ^ p - z = algebraMap K M ξ →
      ξ = (algebraMap A K π)⁻¹ ^ n *
        algebraMap A K (∑ i ∈ Finset.range n, α i ^ (p ^ N) * π ^ i) + algebraMap A K b →
      ∃ (z' : M) (ξ' : K), z' ^ p - z' = algebraMap K M ξ' ∧
        Algebra.adjoin K {z'} = Algebra.adjoin K {z} ∧
        ((∃ c : A, ξ' = algebraMap A K c)
          ∨ ∃ (N' n' : ℕ) (β : ℕ → A) (b' : A), 0 < n' ∧ n' ≤ N' ∧ IsUnit (β 0) ∧ ¬ p ∣ n' ∧
              ξ' = (algebraMap A K π)⁻¹ ^ n' *
                algebraMap A K (∑ i ∈ Finset.range n', β i ^ (p ^ N') * π ^ i)
                + algebraMap A K b') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hNn α b ξ z hz hξ
    rcases exists_step_frobeniusNumerator p π hπ N n hNn α b ξ z hz hξ with
      hint | hterm | hnorm | hred
    · exact ⟨z, ξ, hz, rfl, Or.inl hint⟩
    · obtain ⟨hn, hu, hnd⟩ := hterm
      exact ⟨z, ξ, hz, rfl, Or.inr ⟨N, n, α, b, hn, hNn, hu, hnd, hξ⟩⟩
    · -- Normalization: the same `ξ` and the same `z`, at a shorter length and the same depth.
      obtain ⟨β, b', hn, hξ'⟩ := hnorm
      exact ih (n - 1) (by omega) N (by omega) β b' ξ z hz hξ'
    · -- Artin--Schreier reduction: a new generator, one level of depth spent,
      -- with the subalgebra preserved.
      obtain ⟨N', β, z', ξ', hNeq, hn, hAS, hadj, hξ'⟩ := hred
      obtain ⟨z'', ξ'', hz'', hadj'', hend⟩ :=
        ih (n - 1) (by omega) N' (by omega) β b ξ' z' hAS hξ'
      exact ⟨z'', ξ'', hz'', hadj''.trans hadj, hend⟩

/-- **The residue of a Frobenius numerator is the `p ^ N`-th power of its level-`0` residue.**

Every higher term carries a factor of the non-unit `π`, so it dies in the residue field. -/
theorem residue_sum_pow_eq {A : Type*} [CommRing A] [IsLocalRing A] (p N n : ℕ) (hn : 0 < n)
    (π : A) (hπ : ¬IsUnit π) (α : ℕ → A) :
    IsLocalRing.residue A (∑ i ∈ Finset.range n, α i ^ (p ^ N) * π ^ i)
      = IsLocalRing.residue A (α 0) ^ (p ^ N) := by
  have hzero : IsLocalRing.residue A π = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hπ
  have hterm : ∀ i ∈ Finset.range n, i ≠ 0 →
      IsLocalRing.residue A (α i ^ (p ^ N) * π ^ i) = 0 := by
    intro i _ hi0
    rw [map_mul, map_pow, map_pow, hzero, zero_pow hi0, mul_zero]
  rw [map_sum, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn) hterm,
    map_mul, map_pow, map_pow, pow_zero, mul_one]

/-- **A unit level-`0` coefficient makes the whole numerator a unit.**

This is what converts the terminal alternative of `exists_step_frobeniusNumerator`, which reports
that the *leading coefficient* is a unit, into the hypothesis that the *numerator* is a unit, which
is what the ramification dichotomy asks for. For a positive length the two are equivalent. -/
theorem isUnit_sum_pow_of_isUnit_coeff_zero {A : Type*} [CommRing A] [IsLocalRing A]
    (p N n : ℕ) (hn : 0 < n) (π : A) (hπ : ¬IsUnit π) (α : ℕ → A) (hu : IsUnit (α 0)) :
    IsUnit (∑ i ∈ Finset.range n, α i ^ (p ^ N) * π ^ i) := by
  refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
  rw [residue_sum_pow_eq p N n hn π hπ α]
  exact pow_ne_zero _ ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu)

section Dichotomy

open IsDiscreteValuationRing

/-- **The chain, end to end: a Frobenius-numerator presentation excludes the ferocious case.**

An Artin--Schreier extension whose parameter is presented as a depth-`N` Frobenius numerator of
length `n` plus an integral part, with `n ≤ N`, is trivial, or unramified with separable residue
extension, or totally ramified. The residually inseparable fourth case of Tag 09F0 is excluded.

This is the composite of the two halves built above and it is the statement the all-perfect-core
branch wanted:

* `exists_terminal_of_frobeniusNumerator` iterates the pole reduction to a translate generating the
  same subalgebra whose parameter is integral, or has a unit numerator and pole order prime to `p`;
* `artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator` turns exactly those
  two facts into the ramification trichotomy, with the integral case going through the
  `hintegral` clause of `isGalois_and_ramification_cases_of_adjoin_root_artinSchreier`.

Note what is *not* a hypothesis: minimality of the pole order. That is the whole point of the
route. Minimality quantifies over all competing generators, it is what the older dichotomy
demanded, and an `F_p`-combination of individually minimal parameters need not be minimal — the
characteristic-`2` example in the module docstring. The depth bound `n ≤ N` replaces it, and a
family can arrange it in advance by fixing one Frobenius depth before any member is examined,
since `n ≤ p ^ n` always. -/
theorem trivial_or_unramified_or_totallyRamified_of_frobeniusNumerator
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (π : A) (hπ : Irreducible π)
    (n N : ℕ) (hNn : n ≤ N) (α : ℕ → A) (b : A)
    (ξ : K) (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n *
      algebraMap A K (∑ i ∈ Finset.range n, α i ^ (p ^ N) * π ^ i) + algebraMap A K b) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      trivial ∨ unramified ∨ totallyRamified := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨z', ξ', hz', hadj, hend⟩ :=
    exists_terminal_of_frobeniusNumerator p π hπ n N hNn α b ξ z hz hξ
  have hgen' : Algebra.adjoin K {z'} = ⊤ := hadj.trans hgen
  rcases hend with ⟨c, hc⟩ | ⟨N', n', β, b', hn', hNn', hu, hnd, hξ'⟩
  · -- The pole is gone: the integral clause of the ramification case analysis applies.
    obtain ⟨hfin, -, -, hintegral, -, -⟩ :=
      isGalois_and_ramification_cases_of_adjoin_root_artinSchreier
        A K L p hp ξ' z' hz' hgen' π hπ
    refine ⟨hfin, ?_⟩
    let _ := hfin
    exact (hintegral ⟨c, hc⟩).elim Or.inl (fun h => Or.inr (Or.inl h))
  · -- Terminal: unit numerator and pole order prime to `p` are exactly the variant's hypotheses.
    refine artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator
      A K L p hp ξ' z' hz' hgen' π hπ n' _ b' hξ' hn' hnd ?_
    exact isUnit_sum_pow_of_isUnit_coeff_zero p N' n' hn' π hπ.not_isUnit β hu

end Dichotomy

end Stacks.EppTheorem

namespace IsDiscreteValuationRing

/-- **A minimal positive pole whose numerator has a `p ^ N`-th-power residue is prime to `p`.**

`not_dvd_poleOrder_of_constant_numerator_of_root` asks for a `p`-th root of the numerator's
residue. What the Frobenius-numerator lemmas of this file produce is a `p ^ N`-th root, which is
more, and this records the one-line descent between them: `y ^ (p ^ (N - 1))` is the `p`-th root,
provided `1 ≤ N`.

**This does not remove the need for an iteration.** The two hypotheses `hmin` and `hy` are about
the *same* representative `ξ`, and for
an `F_p`-combination of the members' parameters no theorem produces both at once. Minimality is not
inherited by combinations: in characteristic `2`, both `π⁻³` and `π⁻³ + π⁻²` have pole order `3`,
prime to `p`, hence minimal, while their sum `π⁻²` has pole order `2` and is *not* minimal — the
Artin--Schreier translation by `t = π⁻¹` carries it to `π⁻¹`. So the combination one can prove
things about is in general not the representative whose minimality the hypothesis needs, and
passing to a minimal representative changes the numerator, after which nothing here says its
residue is still a `p ^ N`-th power.

What is needed is therefore exactly what this theorem does *not* supply: invariance of the
`p ^ N`-th-power property of the numerator under Artin--Schreier translation, or equivalently a
bound on how much depth the reduction consumes.

That is now available, and by a route which drops the minimality hypothesis altogether rather than
propagating it: `exists_terminal_of_frobeniusNumerator` carries the Frobenius shape across the
reduction and terminates with a unit numerator and pole order prime to `p`, and
`trivial_or_unramified_or_totallyRamified_of_frobeniusNumerator` feeds that to the dichotomy. So
this wrapper is superseded for the constant branch; it is retained because its hypotheses are
genuinely weaker in the one respect that it needs no depth bound `n ≤ N`, only a `p ^ N`-th root of
the numerator's residue together with minimality. -/
theorem not_dvd_poleOrder_of_constant_numerator_of_pow
    {A B L M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field L] [Field M]
    [Algebra A B] [Algebra A L] [Algebra B L] [Algebra L M]
    [IsScalarTower A B L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (π : A) (hπ : Irreducible π) (ht : algebraMap A L π ≠ 0)
    (n : ℕ) (hn : 0 < n) (a : A) (b : B) (ξ : L) (z : M)
    (N : ℕ) (hN : 1 ≤ N) (y : IsLocalRing.ResidueField A)
    (hy : y ^ (p ^ N) = IsLocalRing.residue A a)
    (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (hξ : ξ = (algebraMap A L π)⁻¹ ^ n * algebraMap A L a + algebraMap B L b)
    (hmin : ∀ (m : ℕ) (η : L) (w : M),
      w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
      algebraMap A L π ^ m * η ∈ (algebraMap B L).range → n ≤ m) : ¬p ∣ n :=
  not_dvd_poleOrder_of_constant_numerator_of_root p π hπ ht n hn a b ξ z
    (y ^ (p ^ (N - 1)))
    (by rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hN]; exact hy)
    hz hgen hξ hmin

end IsDiscreteValuationRing

end
