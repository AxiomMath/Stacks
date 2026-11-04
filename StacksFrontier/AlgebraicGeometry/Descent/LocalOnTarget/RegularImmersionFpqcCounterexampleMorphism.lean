module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexample
public import StacksCore.Tactic.StacksAttribute

/-!
# The counterexample morphism to the unconditional form of Stacks tag 0694, constructed

`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexample` proves
that no morphism of schemes to `Spec ℤ` whose range is the set of closed points is an immersion,
but it does not exhibit such a morphism: its
`Stacks.Descent.not_isImmersion_of_range_eq_closedPointsSpecInt` is conditional on the hypothesis
`Set.range f.base = closedPointsSpecInt`. This file constructs the morphism and discharges that
hypothesis, so the half "`¬ 𝒫 f`" of the counterexample becomes a statement about an explicitly
given morphism rather than about a hypothetical one.

The morphism is `f : ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ`, the coproduct over the prime numbers of the closed
immersions cut out by `p`.

## Main results

* `Stacks.Descent.range_sigmaDesc_base`: the range of a morphism out of a coproduct of schemes is
  the union of the ranges of its components. This is the bookkeeping the counterexample needs from
  Mathlib's arbitrary coproducts of schemes (`AlgebraicGeometry.sigmaMk`).
* `Stacks.Descent.range_primeResidueHom`: the range of `Spec 𝔽ₚ ⟶ Spec ℤ` is the single point
  `(p)`. The map is surjective, so its range is the zero locus of its kernel `(p)`, and `(p)` is a
  maximal ideal of `ℤ`, so the only prime containing it is itself.
* `Stacks.Descent.range_counterexampleHom`: the range of `f` is `closedPointsSpecInt`, because a
  nonzero prime ideal of `ℤ` is `(p)` for a prime number `p`.
* `Stacks.Descent.not_isImmersion_counterexampleHom`: **`f` is not an immersion**, with no
  hypotheses. Hence none of the three conditions of Stacks tag 063J holds for `f`, which is
  `Stacks.Descent.not_koszulRegularImmersion_counterexampleHom`,
  `Stacks.Descent.not_h1RegularImmersion_counterexampleHom` and
  `Stacks.Descent.not_quasiRegularImmersion_counterexampleHom`, each stated in the shape the
  clauses registered for Stacks tag 0694 carry.

## Implementation notes

This is the `¬ 𝒫 f` half of the counterexample. The other half, that the base change of `f`
along the fpqc covering `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ` is a Koszul-regular, `H₁`-regular and
quasi-regular immersion, is `Stacks.Descent.immersionProperty_counterexampleBaseChangeHom`, and
the two are combined in `Stacks.Descent.not_isLocalAtTarget_koszulRegularImmersion_fpqc` and its
two companions.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Section 35.24 (Tag 02YL)](https://stacks.math.columbia.edu/tag/02YL)
* [Stacks Project, Definition 31.22.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.Descent

universe u

/-! ### The range of a morphism out of a coproduct -/

/-- The range of a morphism out of a coproduct of schemes is the union of the ranges of its
components, because every point of the coproduct lies in one of the components. -/
theorem range_sigmaDesc_base {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (α : ∀ i, X i ⟶ Y) :
    Set.range (Sigma.desc α).base = ⋃ i, Set.range (α i).base := by
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk X).surjective p
    refine ⟨i, x, ?_⟩
    rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · rintro ⟨i, x, rfl⟩
    exact ⟨Sigma.ι X i x, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

/-! ### The members of the counterexample family -/

/-- The `p`-th member of the counterexample family: the closed immersion `Spec 𝔽ₚ ⟶ Spec ℤ` cut
out by the prime `p`. -/
noncomputable def primeResidueHom (p : Nat.Primes) :
    Spec (CommRingCat.of (ZMod p)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))

/-- The ideal `(p)` of `ℤ` is maximal, for `p` a prime number. -/
theorem isMaximal_span_singleton_prime (p : ℕ) (hp : p.Prime) :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible
    ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).irreducible)

/-- The range of `Spec 𝔽ₚ ⟶ Spec ℤ` is the single point `(p)`. The ring map is surjective, so the
range is the zero locus of its kernel `(p)`; and `(p)` is maximal, so the only prime of `ℤ`
containing it is itself. -/
theorem range_primeResidueHom (p : Nat.Primes) :
    Set.range (primeResidueHom p).base = {primePointSpecInt (p : ℕ) p.2} := by
  have hker : RingHom.ker (Int.castRingHom (ZMod (p : ℕ))) = Ideal.span {((p : ℕ) : ℤ)} := by
    simpa using ZMod.ker_intCastRingHom (p : ℕ)
  have hrange : Set.range (primeResidueHom p).base
      = PrimeSpectrum.zeroLocus (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) := by
    rw [← hker]
    exact _root_.range_comap_of_surjective _ _ ZMod.intCast_surjective
  rw [hrange]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff, Set.le_eq_subset,
    ← PrimeSpectrum.asIdeal_le_asIdeal]
  exact ⟨fun hle => PrimeSpectrum.ext
    ((isMaximal_span_singleton_prime (p : ℕ) p.2).eq_of_le x.2.ne_top hle).symm,
    fun h => h ▸ le_rfl⟩

/-! ### The counterexample morphism -/

/-- **The counterexample morphism to the unconditional form of Stacks tag 0694.** The coproduct
over the prime numbers of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤ` cut out by `p`. -/
noncomputable def counterexampleHom :
    (∐ fun p : Nat.Primes => Spec (CommRingCat.of (ZMod p))) ⟶ Spec (CommRingCat.of ℤ) :=
  Sigma.desc primeResidueHom

/-- Every nonzero prime ideal of `ℤ` is `(p)` for a prime number `p`: the closed points of
`Spec ℤ` are exactly the points `(p)`. -/
theorem closedPointsSpecInt_eq_iUnion :
    closedPointsSpecInt = ⋃ p : Nat.Primes, {primePointSpecInt (p : ℕ) p.2} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal x.asIdeal
    have hg' : x.asIdeal = Ideal.span {g} := hg
    have hg0 : g ≠ 0 := by
      intro h
      exact hx (by simpa [hg', h] using (rfl : Ideal.span {(0 : ℤ)} = ⊥))
    have hgp : Prime g := by
      rw [← Ideal.span_singleton_prime hg0, ← hg']
      exact x.2
    refine ⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp⟩, PrimeSpectrum.ext ?_⟩
    rw [hg']
    exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g)
  · rintro ⟨p, rfl⟩
    exact primePointSpecInt_mem (p : ℕ) p.2

/-- **The range of the counterexample morphism is the set of closed points of `Spec ℤ`.** -/
theorem range_counterexampleHom :
    Set.range counterexampleHom.base = closedPointsSpecInt := by
  rw [counterexampleHom, range_sigmaDesc_base, closedPointsSpecInt_eq_iUnion]
  exact Set.iUnion_congr range_primeResidueHom

/-! ### The conclusion: the counterexample morphism is not an immersion -/

/-- **The counterexample morphism is not an immersion.** Its range is the set of closed points of
`Spec ℤ`, which is dense and not open, hence not locally closed, while an immersion has locally
closed range. This is the half `¬ 𝒫 f` of the counterexample to Stacks tag 0694, now with no
hypotheses. -/
theorem not_isImmersion_counterexampleHom : ¬ IsImmersion counterexampleHom :=
  not_isImmersion_of_range_eq_closedPointsSpecInt _ range_counterexampleHom

/-- The counterexample morphism is not a Koszul-regular immersion, since it is not an immersion.
The property is written in the shape carried by the clauses registered for Stacks tag 0694. -/
theorem not_koszulRegularImmersion_counterexampleHom :
    ¬ ∃ hf : IsImmersion counterexampleHom,
        @IsKoszulRegularImmersion _ _ counterexampleHom hf :=
  fun h => not_isImmersion_counterexampleHom h.1

/-- The counterexample morphism is not an `H₁`-regular immersion, since it is not an immersion. -/
theorem not_h1RegularImmersion_counterexampleHom :
    ¬ ∃ hf : IsImmersion counterexampleHom,
        @IsH1RegularImmersion _ _ counterexampleHom hf :=
  fun h => not_isImmersion_counterexampleHom h.1

/-- The counterexample morphism is not a quasi-regular immersion, since it is not an immersion. -/
theorem not_quasiRegularImmersion_counterexampleHom :
    ¬ ∃ hf : IsImmersion counterexampleHom,
        @IsQuasiRegularImmersion _ _ counterexampleHom hf :=
  fun h => not_isImmersion_counterexampleHom h.1

end Stacks.Descent

end
