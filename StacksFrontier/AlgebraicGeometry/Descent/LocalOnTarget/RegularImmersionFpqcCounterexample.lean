module

public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# Ingredients of the counterexample to the unconditional form of Stacks tag 0694

Stacks tag 0694 asserts that each of the three conditions Koszul-regular, `H₁`-regular and
quasi-regular on an immersion of schemes is local on the target for the fpqc topology. Being
local on the target means, by Stacks tag 02KO, an equivalence for *every* morphism of schemes
`f : X ⟶ S` and every fpqc covering of `S`; in particular it contains the fpqc descent of the
property of being an immersion. That descent is false, so tag 0694 read literally is false. The
module docstring of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcOfImmersion` states
the counterexample and places it against the Stacks Project's own Section 35.24 (tag 02YL),
which collects being an immersion among the properties it "could not (yet)" show fpqc local on
the base.

The counterexample is `f : ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ`, the coproduct over the prime numbers of the
closed immersions cut out by `p`, against the one-member fpqc covering
`Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`. This file formalizes the two halves of it that are independent of the
scheme-theoretic bookkeeping.

## Main results

The failure of the conclusion, `¬ 𝒫 f`:

* `Stacks.Descent.not_isLocallyClosed_closedPointsSpecInt`: the set of closed points of
  `Spec ℤ` is not locally closed. It is dense, because an integer lying in every nonzero prime
  of `ℤ` is zero, so a locally closed set equal to it is open; and it is not open, because its
  complement is the generic point, which is not a closed point.
* `Stacks.Descent.not_isImmersion_of_range_eq_closedPointsSpecInt`: consequently no morphism of
  schemes to `Spec ℤ` whose range is that set is an immersion, since an immersion has locally
  closed range. The morphism `f` above has exactly that range, so none of the three conditions
  of Stacks tag 063J holds for it.

The covering, and the base change along it:

* `Stacks.Descent.faithfullyFlat_int_padicIntProd`: `∏ₚ ℤₚ` is faithfully flat over `ℤ`.
  Flatness is automatic from Mathlib — the product is torsion-free and `ℤ` is a Bezout domain —
  and faithfulness is the statement that a prime generating a maximal ideal of `ℤ` is not a unit
  in the product, which is read off its own adic factor.
* `Stacks.Descent.flat_and_surjective_specMap_padicIntProd`: hence `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ` is
  flat and surjective between affine schemes, which is what makes `{Spec (∏ₚ ℤₚ) ⟶ Spec ℤ}` an
  fpqc covering.
* `Stacks.Descent.padicIntProdQuotEquiv`: `(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`, the computation which
  identifies the base change of `f` along that covering as `∐ₚ Spec 𝔽ₚ ⟶ Spec (∏ₚ ℤₚ)`. Its
  content is that `p` is a unit in `ℤ_q` for every prime `q ≠ p`, so the ideal `p (∏ₚ ℤₚ)` is
  everything outside the `p`-th factor and `p ℤₚ` inside it.

## Implementation notes

The counterexample is assembled in three further modules. The morphism `f` is constructed and
shown not to be an immersion (`Stacks.Descent.not_isImmersion_counterexampleHom`), discharging
the hypothesis of `Stacks.Descent.not_isImmersion_of_range_eq_closedPointsSpecInt` below. Its
base change along the covering is identified as the coproduct of the closed immersions
`Spec 𝔽ₚ ⟶ Spec (∏ₚ ℤₚ)` (`Stacks.Descent.isPullback_counterexampleBaseChange`), which is shown
to be a Koszul-regular, `H₁`-regular and quasi-regular immersion; the three conditions are then
refuted as fpqc local on the target in
`Stacks.Descent.not_isLocalAtTarget_koszulRegularImmersion_fpqc`,
`Stacks.Descent.not_isLocalAtTarget_h1RegularImmersion_fpqc` and
`Stacks.Descent.not_isLocalAtTarget_quasiRegularImmersion_fpqc`.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Definition 35.22.1 (Tag 02KO)](https://stacks.math.columbia.edu/tag/02KO)
* [Stacks Project, Lemma 35.22.4 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Section 35.24 (Tag 02YL)](https://stacks.math.columbia.edu/tag/02YL)
* [Stacks Project, Definition 31.22.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Descent

/-- A prime number, packaged as an element of `Nat.Primes`, satisfies the `Fact` hypothesis the
`p`-adic integers are indexed by. -/
instance instFactPrimeNatPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### The set of closed points of `Spec ℤ` is not locally closed -/

/-- The set of closed points of `Spec ℤ`, that is, the primes of `ℤ` other than `(0)`. -/
def closedPointsSpecInt : Set (PrimeSpectrum ℤ) := {x | x.asIdeal ≠ ⊥}

/-- The generic point of `Spec ℤ`, the prime `(0)`. -/
def genericPointSpecInt : PrimeSpectrum ℤ :=
  ⟨⊥, ⟨by simp, fun {x y} hxy => by simpa [Ideal.mem_bot, mul_eq_zero] using hxy⟩⟩

/-- The closed points of `Spec ℤ` are the complement of the generic point. -/
theorem closedPointsSpecInt_eq_compl :
    closedPointsSpecInt = ({genericPointSpecInt} : Set (PrimeSpectrum ℤ))ᶜ := by
  ext x
  simp only [closedPointsSpecInt, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun h hx => h (congrArg PrimeSpectrum.asIdeal hx), fun h hx => h (PrimeSpectrum.ext hx)⟩

/-- The point of `Spec ℤ` given by a prime number. -/
def primePointSpecInt (p : ℕ) (hp : p.Prime) : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)⟩

/-- The point of `Spec ℤ` given by a prime number is a closed point. -/
theorem primePointSpecInt_mem (p : ℕ) (hp : p.Prime) :
    primePointSpecInt p hp ∈ closedPointsSpecInt := by
  simpa [closedPointsSpecInt, primePointSpecInt, Ideal.span_singleton_eq_bot] using hp.ne_zero

/-- An integer lying in every nonzero prime of `ℤ` is zero: the closed points of `Spec ℤ` have
vanishing ideal `(0)`. -/
theorem vanishingIdeal_closedPointsSpecInt :
    PrimeSpectrum.vanishingIdeal closedPointsSpecInt = ⊥ := by
  refine le_antisymm (fun n hn => ?_) bot_le
  rw [PrimeSpectrum.mem_vanishingIdeal] at hn
  simp only [Ideal.mem_bot]
  by_contra hn0
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  have hmem := hn _ (primePointSpecInt_mem p hp)
  simp only [primePointSpecInt, Ideal.mem_span_singleton] at hmem
  have : p ∣ n.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hmem
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
  omega

/-- The closed points of `Spec ℤ` are dense: their closure is everything. -/
theorem closure_closedPointsSpecInt : closure closedPointsSpecInt = Set.univ := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_closedPointsSpecInt]
  exact PrimeSpectrum.zeroLocus_bot

/-- The zero ideal of `ℤ` is not maximal. -/
theorem not_isMaximal_bot_int : ¬ (⊥ : Ideal ℤ).IsMaximal := by
  intro h
  have h2 : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
    simp only [ne_eq, Ideal.span_singleton_eq_top, Int.isUnit_iff]
    omega
  have := h.eq_of_le h2 bot_le
  rw [eq_comm, Ideal.span_singleton_eq_bot] at this
  omega

/-- The closed points of `Spec ℤ` are not an open set: the generic point is not closed. -/
theorem not_isOpen_closedPointsSpecInt : ¬ IsOpen closedPointsSpecInt := by
  rw [closedPointsSpecInt_eq_compl, isOpen_compl_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact not_isMaximal_bot_int

/-- **The topological obstruction to Stacks tag 0694.** The set of closed points of `Spec ℤ` is
not locally closed: it is dense, so a locally closed set equal to it would have to be open, and
it is not open because the generic point of `Spec ℤ` is not a closed point. -/
theorem not_isLocallyClosed_closedPointsSpecInt : ¬ IsLocallyClosed closedPointsSpecInt := by
  rintro ⟨U, Z, hU, hZ, hs⟩
  have hsub : closure closedPointsSpecInt ⊆ Z := by
    rw [hZ.closure_subset_iff, hs]
    exact Set.inter_subset_right
  rw [closure_closedPointsSpecInt, Set.univ_subset_iff] at hsub
  rw [hsub, Set.inter_univ] at hs
  exact not_isOpen_closedPointsSpecInt (hs ▸ hU)

/-- **The morphism of the counterexample to Stacks tag 0694 is not an immersion.** Any morphism
of schemes to `Spec ℤ` whose range is the set of closed points -- such as the coproduct over the
primes `p` of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤ` -- fails to be an immersion, because an
immersion has locally closed range. -/
theorem not_isImmersion_of_range_eq_closedPointsSpecInt {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℤ))
    (hf : Set.range f.base = closedPointsSpecInt) : ¬ IsImmersion f :=
  fun _ => not_isLocallyClosed_closedPointsSpecInt (hf ▸ f.isLocallyClosed_range)

/-! ### The covering of the counterexample: `ℤ ⟶ ∏ₚ ℤₚ` is faithfully flat -/

/-- For distinct primes `p` and `q`, the prime `p` is a unit in the `q`-adic integers. -/
theorem isUnit_natCast_padicInt_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    [Fact q.Prime] : IsUnit ((p : ℕ) : ℤ_[q]) := by
  by_contra h
  have hlt := PadicInt.not_isUnit_iff.mp h
  have : ((q : ℕ) : ℤ) ∣ p := (PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast this)).symm

/-- Every element of `∏ₚ ℤₚ` whose `p`-th coordinate is divisible by `p` is divisible by `p`:
away from the `p`-th factor, `p` is a unit. -/
theorem padicIntProd_dvd_of_dvd_eval (p : Nat.Primes) (b : ∀ q : Nat.Primes, ℤ_[q])
    (hb : ((p : ℕ) : ℤ_[p]) ∣ b p) : ((p : ℕ) : ∀ q : Nat.Primes, ℤ_[q]) ∣ b := by
  have hq : ∀ q : Nat.Primes, ((p : ℕ) : ℤ_[q]) ∣ b q := by
    intro q
    by_cases h : p = q
    · subst h
      exact hb
    · exact (isUnit_natCast_padicInt_of_ne p.2 q.2
        (fun hpq => h (Nat.Primes.coe_nat_inj p q |>.mp hpq))).dvd
  refine ⟨fun q => (hq q).choose, funext fun q => ?_⟩
  simpa using (hq q).choose_spec

/-- The `p`-th residue map of `∏ₚ ℤₚ`: evaluate at `p`, then reduce mod `p`. -/
noncomputable def padicIntProdResidue (p : Nat.Primes) :
    (∀ q : Nat.Primes, ℤ_[q]) →+* ZMod p :=
  PadicInt.toZMod.comp (Pi.evalRingHom (fun q : Nat.Primes => ℤ_[q]) p)

/-- The `p`-th residue map of `∏ₚ ℤₚ` is surjective. -/
theorem padicIntProdResidue_surjective (p : Nat.Primes) :
    Function.Surjective (padicIntProdResidue p) :=
  (ZMod.ringHom_surjective PadicInt.toZMod).comp (Function.surjective_eval p)

/-- The kernel of the `p`-th residue map of `∏ₚ ℤₚ` is the ideal generated by `p`. -/
theorem ker_padicIntProdResidue (p : Nat.Primes) :
    RingHom.ker (padicIntProdResidue p) =
      Ideal.span {((p : ℕ) : ∀ q : Nat.Primes, ℤ_[q])} := by
  ext b
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro h
    refine padicIntProd_dvd_of_dvd_eval p b ?_
    have hker : b p ∈ RingHom.ker (PadicInt.toZMod (p := (p : ℕ))) := h
    rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hker
  · rintro ⟨c, rfl⟩
    simp [padicIntProdResidue]

/-- `(∏ₚ ℤₚ) ⧸ p (∏ₚ ℤₚ) ≅ 𝔽ₚ`. This is the computation that identifies the base change of the
counterexample's morphism along the covering `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`. -/
noncomputable def padicIntProdQuotEquiv (p : Nat.Primes) :
    ((∀ q : Nat.Primes, ℤ_[q]) ⧸ Ideal.span {((p : ℕ) : ∀ q : Nat.Primes, ℤ_[q])}) ≃+*
      ZMod p :=
  (Ideal.quotEquivOfEq (ker_padicIntProdResidue p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (padicIntProdResidue_surjective p))

/-! ### Flatness and faithful flatness of `ℤ ⟶ ∏ₚ ℤₚ` -/

/-- `∏ₚ ℤₚ` is faithfully flat over `ℤ`. Flatness is automatic: the product is torsion-free and
`ℤ` is a Bezout domain. For the faithfulness, a maximal ideal of `ℤ` is `(g)` for a prime `g`, and
`g` is not a unit in `∏ₚ ℤₚ` because it is not a unit in the `|g|`-adic factor. -/
instance faithfullyFlat_int_padicIntProd :
    Module.FaithfullyFlat ℤ (∀ p : Nat.Primes, ℤ_[p]) := by
  refine ⟨fun {m} hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, ne_eq, Submodule.restrictScalars_eq_top_iff]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal m
  have hg0 : g ≠ 0 := fun h => not_isMaximal_bot_int (by simpa [hg, h] using hm)
  have hg' : m = Ideal.span {g} := hg
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, ← hg']
    exact hm.isPrime
  have hq : (g.natAbs).Prime := Int.prime_iff_natAbs_prime.mp hgp
  have : Fact (g.natAbs).Prime := ⟨hq⟩
  intro htop
  rw [hg', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at htop
  have hunit : IsUnit ((algebraMap ℤ ℤ_[g.natAbs]) g) :=
    htop.map (Pi.evalRingHom (fun q : Nat.Primes => ℤ_[q]) ⟨g.natAbs, hq⟩)
  have hdvd : ((g.natAbs : ℕ) : ℤ) ∣ g := Int.natAbs_dvd.mpr dvd_rfl
  have hlt : ‖((g : ℤ) : ℤ_[g.natAbs])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd
  have heq : ‖((g : ℤ) : ℤ_[g.natAbs])‖ = 1 := by
    simpa [algebraMap_int_eq, eq_intCast] using PadicInt.isUnit_iff.mp hunit
  exact hlt.ne heq

/-- **The covering of the counterexample to Stacks tag 0694.** `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ` is flat
and surjective between affine schemes, hence a one-member fpqc covering of `Spec ℤ`. -/
theorem flat_and_surjective_specMap_padicIntProd :
    Flat (Spec.map (CommRingCat.ofHom
        (algebraMap ℤ (∀ p : Nat.Primes, ℤ_[p])))) ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (algebraMap ℤ (∀ p : Nat.Primes, ℤ_[p])))) :=
  (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

end Stacks.Descent

end
