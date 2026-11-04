module

public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresFiniteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of local cohomology below a degree as a criterion for the cutoff

Let `A` be a universally catenary Noetherian ring, let `I ⊆ A` be an ideal, let `Z = V(I)` and
let `M` be a finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness
cutoff of Tag 0BJR. Fix `n : ℕ` and assume the formal fibres of the local rings of `A` satisfy
Serre's condition `(Sₙ)`. Then

`n < s` if and only if `H^i_Z(M)` is a finite `A`-module for every degree `i ≤ n`,

and equivalently for every degree of the form `p + 1` with `p < n`, the cutoff being at least
`1` in all cases.

The two implications are the two clauses of Tag 0BJW: finiteness below the cutoff gives one
direction outright, and non-finiteness in the cutoff degree gives the other by contraposition,
the single `(Sₙ)` hypothesis covering the `(S_{s-1})` needed there because `s ≤ n`.

## Main results

* `Stacks.LocalCohomology.FormalFibersHavePropertySk.mono` — Serre's condition on the formal
  fibres weakens as the index decreases.
* `Stacks.LocalCohomology.one_le_localCohomologyCutoff` — the cutoff is never `0`.
* `Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite` — the equivalence above.
* `Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succ` — the same
  equivalence with the degrees written as `p + 1` for `p < n`.

## Implementation notes

This is the ring-theoretic content of Tag 0BJY: over `A` with `Z = V(I)`, condition (a) of that
tag is the inequality `n < s_{A,I}(M)`, Tag 0BJR identifying the minimum of the expressions
`depth(ℱ_x) + dim(𝒪_{closure{x}, z})` with the cutoff, and condition (b) is finiteness of
`H^{p+1}_Z(M)` for `0 ≤ p < n` by Tag 0BK0 — which is the indexing of
`lt_localCohomologyCutoff_iff_forall_finite_succ`. Degree `0` costs nothing in the first form,
`H^0_Z(M)` being a submodule of `M`, so the two forms agree; what makes them equivalent here is
`one_le_localCohomologyCutoff`, which rules out the one value of the cutoff that the shifted
indexing cannot see.

The cutoff is an infimum in `ℕ∞`, so `s = ⊤` when no admissible pair of primes exists; the
statements are correct there, both sides holding for every `n`. The hypothesis on the formal
fibres is imposed at the single index `n`, which by
`Stacks.LocalCohomology.FormalFibersHavePropertySk.mono` is the weakest index at which both
clauses of Tag 0BJW are available for the degrees in question.

Local cohomology is taken in the model `Stacks.LocalCohomology.localCohomologyWithSupportIn`
for the support `V(I) = PrimeSpectrum.zeroLocus I`, which is the model Tag 0BJW is stated in.

## References

* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- Serre's condition `(Sₖ)` for a ring weakens as `k` decreases: the bound it imposes on the
depth of a localization is `min(k, dim)`, which is monotone in `k`. -/
@[ega "IV 5.7.3" "special case"]
private lemma propertySkRing_mono {R : Type*} [CommRing R] [IsNoetherianRing R] {j k : ℕ}
    (h : PropertySkRing R k) (hjk : j ≤ k) : PropertySkRing R j := fun p _ =>
  le_trans (min_le_min_right _ (Nat.cast_le.mpr hjk)) (h p)

/-- Serre's condition `(Sₖ)` on the formal fibres of a local ring weakens as `k` decreases. -/
public lemma FormalFibersHavePropertySk.mono {A : Type u} [CommRing A] [IsLocalRing A] {j k : ℕ}
    (h : FormalFibersHavePropertySk A k) (hjk : j ≤ k) : FormalFibersHavePropertySk A j := by
  intro p hp
  obtain ⟨hF, hSk⟩ := h p
  exact ⟨hF, @propertySkRing_mono _ _ hF _ _ hSk hjk⟩

/-- An element of `ℕ∞` bounded by a natural number is one, and is bounded by it as such. -/
private lemma exists_nat_eq_of_le_natCast {x : ℕ∞} {n : ℕ} (h : x ≤ (n : ℕ∞)) :
    ∃ s : ℕ, x = (s : ℕ∞) ∧ s ≤ n := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact absurd h (by simp)
  · obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hx
    refine ⟨s, hs.symm, ?_⟩
    rw [← hs] at h
    exact_mod_cast h

/-- The local cohomology finiteness cutoff is at least `1`. An admissible pair of primes
`𝔭 ⊆ 𝔮` has `𝔭 ∉ V(I)` and `𝔮 ∈ V(I)`, hence `𝔭 ≠ 𝔮`, so the image of `𝔮` in the domain `A/𝔭`
is a nonzero prime and already contributes height at least `1`. -/
public theorem one_le_localCohomologyCutoff (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] : 1 ≤ localCohomologyCutoff A I M := by
  rw [le_localCohomologyCutoff_iff]
  intro p q hp hq hpq
  have hne : p.asIdeal ≠ q.asIdeal := fun h => hp (h ▸ hq)
  have : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)) ≠ ⊥ := by
    intro hbot
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot
    exact hne (le_antisymm hpq hbot)
  have hdom : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  have hone : 1 ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    Order.one_le_iff_ne_zero.mpr fun h0 => this (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  exact hone.trans le_add_self

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The cutoff criterion for finiteness of local cohomology.** Let `A` be a universally
catenary Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `M` a finite `A`-module. If the
formal fibres of the local rings of `A` satisfy Serre's condition `(Sₙ)`, then the cutoff
`s = s_{A,I}(M)` of Tag 0BJR exceeds `n` exactly when `H^i_Z(M)` is a finite `A`-module in
every degree `i ≤ n`.

Forwards this is the finiteness clause of Tag 0BJW. Backwards, if `s ≤ n` then `s` is a natural
number, the formal fibres satisfy `(S_{s-1})` because `s - 1 ≤ n`, and the non-finiteness clause
of Tag 0BJW makes `H^s_Z(M)` infinite in a degree `s ≤ n`. -/
public theorem lt_localCohomologyCutoff_iff_forall_finite
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n) :
    (n : ℕ∞) < localCohomologyCutoff A I M ↔
      ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  refine ⟨fun hn =>
    finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers
      A I M hA n hformal hn, fun h => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, hs, hsn⟩ := exists_nat_eq_of_le_natCast hcon
  exact not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers
    A I M hA s (fun p => (hformal p).mono (by omega)) hs
    (h (s : ℤ) (by exact_mod_cast hsn))

/-- **The cutoff criterion in the degrees Tag 0BK0 produces.** In the situation of
`lt_localCohomologyCutoff_iff_forall_finite`, the cutoff exceeds `n` exactly when `H^{p+1}_Z(M)`
is a finite `A`-module for every `p < n`.

The degrees `i ≤ 0` of the previous form are not needed: `one_le_localCohomologyCutoff` makes
the cutoff at least `1`, so a cutoff bounded by `n` is a positive natural number `s`, and `s`
is the successor of the degree `s - 1 < n` supplied here. -/
public theorem lt_localCohomologyCutoff_iff_forall_finite_succ
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n) :
    (n : ℕ∞) < localCohomologyCutoff A I M ↔
      ∀ p : ℕ, p < n → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
          ((p + 1 : ℕ) : ℤ)) := by
  refine ⟨fun hn p hp => (lt_localCohomologyCutoff_iff_forall_finite A I M hA n hformal).mp hn
    ((p + 1 : ℕ) : ℤ) (by exact_mod_cast hp), fun h => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, hs, hsn⟩ := exists_nat_eq_of_le_natCast hcon
  have hs1 : 1 ≤ s := by exact_mod_cast hs ▸ one_le_localCohomologyCutoff A I M
  exact not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers
    A I M hA s (fun p => (hformal p).mono (by omega)) hs
    (Nat.sub_add_cancel hs1 ▸ h (s - 1) (by omega))

end Stacks.LocalCohomology

end
