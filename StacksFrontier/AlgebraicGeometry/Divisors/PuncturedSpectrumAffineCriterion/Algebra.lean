module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion.Artinian

/-!
# The algebraic heart of the affineness criterion for a punctured spectrum

This file isolates the ring-theoretic content of the hard implication of Stacks Tag 0BCR.  Let
`A` be a Noetherian local ring with maximal ideal `𝔪` and let `B` be an `A`-algebra which behaves
like the ring of functions on the punctured spectrum of `A`:

* `𝔪 B = B`;
* for every `g ∈ 𝔪`, every element of `B` is carried into the image of `A` by a power of `g`
  (equivalently `B ⧸ A` is `g`-power torsion, which holds because `A → B` becomes an isomorphism
  after inverting any `g ∈ 𝔪`).

If moreover some `f ∈ 𝔪` acts injectively on `B`, then `f` generates the unit ideal of `B`.
Geometrically: the vanishing locus of `f` on the punctured spectrum is empty, so `f` cuts out
exactly the closed point and `dim A ≤ 1` by Krull's principal ideal theorem.

The proof is the argument of the Stacks Project.  Writing `Q = B ⧸ A`, the submodule
`Sₙ = {b | fⁿ b ∈ A}` embeds in `A` by `b ↦ fⁿ b`, so each `Q[fⁿ]` is a finitely generated
`A`-module; the torsion hypothesis makes `Q[f]` supported at the closed point, hence Artinian.
Therefore `Q = Q[f^{n₀}] + fQ` for some `n₀`, so `B ⧸ fB` is a finite `A`-module and
`Spec (B ⧸ fB) → Spec A` has closed image.  That image avoids the closed point because
`𝔪 B = B`, while a nonempty closed subset of the spectrum of a local ring contains the closed
point.  So `B ⧸ fB` is the zero ring.

## Main results

* `Stacks.Divisors.span_singleton_eq_top_of_forall_exists_pow_smul_mem_range`

## References

* [Stacks Project, Tag 0BCR](https://stacks.math.columbia.edu/tag/0BCR)
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Stacks.Divisors

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- For `f : A` and `n : ℕ`, the `A`-submodule of `B` consisting of those `b` for which `fⁿ • b`
lies in the image of `A`.  Its image in `B ⧸ A` is the `fⁿ`-torsion. -/
private def smulMemRange (f : A) (n : ℕ) : Submodule A B :=
  (LinearMap.range (Algebra.linearMap A B)).comap (LinearMap.lsmul A B (f ^ n))

private lemma mem_smulMemRange {f : A} {n : ℕ} {b : B} :
    b ∈ smulMemRange f n ↔ ∃ a : A, algebraMap A B a = f ^ n • b := by
  simp [smulMemRange]

private lemma range_le_smulMemRange (f : A) (n : ℕ) :
    LinearMap.range (Algebra.linearMap A B) ≤ smulMemRange f n := by
  rintro _ ⟨a, rfl⟩
  exact mem_smulMemRange.2 ⟨f ^ n * a, by simp [Algebra.smul_def]⟩

/-- Multiplication by `fⁿ` embeds `Sₙ = {b | fⁿ b ∈ A}` into the image of `A`, a Noetherian
`A`-module, as soon as `f` acts injectively on `B`; hence `Sₙ` is a finitely generated
`A`-module. -/
private lemma finite_smulMemRange [IsNoetherianRing A] {f : A}
    (hfB : algebraMap A B f ∈ nonZeroDivisors B) (n : ℕ) :
    Module.Finite A (smulMemRange (B := B) f n) := by
  have hreg : (algebraMap A B) (f ^ n) ∈ nonZeroDivisors B := by
    rw [map_pow]
    exact pow_mem hfB n
  let u : smulMemRange (B := B) f n →ₗ[A] LinearMap.range (Algebra.linearMap A B) :=
    (LinearMap.lsmul A B (f ^ n)).restrict (fun _ hx => hx)
  have hu : Function.Injective u := by
    intro x y hxy
    have h : f ^ n • (x : B) = f ^ n • (y : B) := congrArg Subtype.val hxy
    refine Subtype.ext (sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hreg).1 _ ?_))
    rw [Algebra.smul_def, Algebra.smul_def] at h
    rw [mul_sub, h, sub_self]
  exact Module.Finite.of_injective u hu

/-- An element of `B ⧸ A` represented by `b` is killed by `fⁿ` iff `b ∈ Sₙ`. -/
private lemma pow_smul_mkQ_eq_zero_iff {f : A} {n : ℕ} {b : B} :
    f ^ n • (LinearMap.range (Algebra.linearMap A B)).mkQ b = 0 ↔ b ∈ smulMemRange f n := by
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact mem_smulMemRange.symm

/-- The `fⁿ`-torsion of `B ⧸ A` is the image of `Sₙ = {b | fⁿ b ∈ A}`. -/
private lemma torsionBy_eq_map_smulMemRange (f : A) (n : ℕ) :
    Submodule.torsionBy A (B ⧸ LinearMap.range (Algebra.linearMap A B)) (f ^ n) =
      Submodule.map (LinearMap.range (Algebra.linearMap A B)).mkQ (smulMemRange f n) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨b, rfl⟩ := (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective q
    exact ⟨b, pow_smul_mkQ_eq_zero_iff.1 ((Submodule.mem_torsionBy_iff _ _).1 hq), rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (Submodule.mem_torsionBy_iff _ _).2 (pow_smul_mkQ_eq_zero_iff.2 hb)

/-- Writing `Q = B ⧸ A`, if `Q = Q[fⁿ] + fQ` then `B = {b | fⁿ b ∈ A} + f B`. -/
private lemma exists_mem_smulMemRange_add_smul {f : A} {n : ℕ}
    (hn : ∀ q : B ⧸ LinearMap.range (Algebra.linearMap A B),
      ∃ q', f ^ n • q' = 0 ∧ ∃ w, q = q' + f • w) (b : B) :
    ∃ s ∈ smulMemRange (B := B) f n, ∃ w : B, b = s + f • w := by
  set T := LinearMap.range (Algebra.linearMap A B)
  obtain ⟨q', hq', w', hw'⟩ := hn (T.mkQ b)
  obtain ⟨s, rfl⟩ := T.mkQ_surjective q'
  obtain ⟨w, rfl⟩ := T.mkQ_surjective w'
  have hs : s ∈ smulMemRange (B := B) f n := pow_smul_mkQ_eq_zero_iff.1 hq'
  have ht : b - (s + f • w) ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_add,
      LinearMap.map_smul, ← hw', sub_self]
  refine ⟨s + (b - (s + f • w)), Submodule.add_mem _ hs (range_le_smulMemRange f n ht), w, ?_⟩
  abel

/-- A nontrivial integral algebra `C` over a local ring `A` has a prime ideal containing the
image of the maximal ideal of `A`. -/
private theorem exists_primeSpectrum_map_maximalIdeal_le [IsLocalRing A] {C : Type*} [CommRing C]
    [Nontrivial C] [Algebra A C] [Algebra.IsIntegral A C] :
    ∃ q : PrimeSpectrum C, Ideal.map (algebraMap A C) (maximalIdeal A) ≤ q.asIdeal := by
  have hint : (algebraMap A C).IsIntegral := Algebra.IsIntegral.isIntegral
  set t := Set.range (PrimeSpectrum.comap (algebraMap A C)) with htdef
  have hclosed : IsClosed t := by
    simpa [htdef] using PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint _ isClosed_univ
  obtain ⟨x, hx⟩ : t.Nonempty := Set.range_nonempty _
  have hvan : PrimeSpectrum.vanishingIdeal t ≤ maximalIdeal A :=
    le_trans (fun a ha => (PrimeSpectrum.mem_vanishingIdeal t a).1 ha x hx)
      (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  have hmem : closedPoint A ∈ t := by
    rw [← hclosed.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hvan
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal hq).ge⟩

/-- **The algebraic core of the hard implication of Stacks 0BCR.**  Let `A` be a Noetherian local
ring and `B` an `A`-algebra such that `𝔪 B = B` and such that every element of `B` is carried
into the image of `A` by a power of each element of `𝔪`.  Then every
`f ∈ 𝔪` acting injectively on `B` generates the unit ideal of `B`.

Writing `Q = B ⧸ A`, each `fⁿ`-torsion submodule of `Q` is finitely generated because
`b ↦ fⁿ b` embeds `{b | fⁿ b ∈ A}` into `A`, and `Q[f]` is annihilated by a power of `𝔪`, hence
Artinian.  So `Q = Q[f^{n₀}] + fQ` for some `n₀` and `B ⧸ fB` is a finite `A`-module.  Were
`B ⧸ fB` nonzero, the closed image of its spectrum in `Spec A` would contain the closed point,
producing a prime of `B ⧸ fB` containing the image of `𝔪` — impossible since `𝔪 B = B`. -/
theorem span_singleton_eq_top_of_forall_exists_pow_smul_mem_range
    [IsLocalRing A] [IsNoetherianRing A]
    (hmB : Ideal.map (algebraMap A B) (maximalIdeal A) = ⊤)
    (htor : ∀ g ∈ maximalIdeal A, ∀ b : B, ∃ (N : ℕ) (a : A), algebraMap A B a = g ^ N • b)
    {f : A} (hfm : f ∈ maximalIdeal A) (hfB : algebraMap A B f ∈ nonZeroDivisors B) :
    Ideal.span {algebraMap A B f} = (⊤ : Ideal B) := by
  classical
  set T := LinearMap.range (Algebra.linearMap A B) with hT
  -- Every element of `B ⧸ A` is killed by a power of every element of the maximal ideal.
  have htorQ : ∀ (q : B ⧸ T), ∀ g ∈ maximalIdeal A, ∃ N : ℕ, g ^ N • q = 0 := by
    intro q g hg
    obtain ⟨b, rfl⟩ := T.mkQ_surjective q
    obtain ⟨N, a, ha⟩ := htor g hg b
    exact ⟨N, pow_smul_mkQ_eq_zero_iff.2 (mem_smulMemRange.2 ⟨a, ha⟩)⟩
  -- Each `fⁿ`-torsion submodule of `B ⧸ A` is a finite `A`-module.
  have hfinT : ∀ n : ℕ, Module.Finite A (Submodule.torsionBy A (B ⧸ T) (f ^ n)) := by
    intro n
    rw [hT, torsionBy_eq_map_smulMemRange]
    exact Module.Finite.of_fg ((Module.Finite.iff_fg.1 (finite_smulMemRange hfB n)).map _)
  -- The `f`-torsion is moreover Artinian: it is finite and supported at the closed point.
  have hart : IsArtinian A (Submodule.torsionBy A (B ⧸ T) f) := by
    have hfin := hfinT 1
    rw [pow_one] at hfin
    refine isArtinian_of_forall_exists_pow_smul_eq_zero fun g hg x => ?_
    obtain ⟨N, hN⟩ := htorQ (x : B ⧸ T) g hg
    exact ⟨N, Subtype.ext (by simpa using hN)⟩
  obtain ⟨n₀, hn₀⟩ := exists_forall_eq_add_smul_of_isArtinian_torsionBy f
    (fun q => htorQ q f hfm) hart
  -- Hence `B = {b | f^{n₀} b ∈ A} + f B`.
  have hgen := exists_mem_smulMemRange_add_smul hn₀
  -- So `B ⧸ fB` is a finite `A`-module.
  by_contra hne
  set I : Ideal B := Ideal.span {algebraMap A B f}
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hfin : Module.Finite A (B ⧸ I) := by
    rw [Module.finite_def]
    have htop : (⊤ : Submodule A (B ⧸ I)) =
        Submodule.map (Ideal.Quotient.mkₐ A I).toLinearMap (smulMemRange (B := B) f n₀) := by
      refine le_antisymm (fun c _ => ?_) le_top
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) c
      obtain ⟨s, hs, w, rfl⟩ := hgen b
      refine ⟨s, hs, ?_⟩
      have hfw : f • w ∈ I := Ideal.mem_span_singleton.2 ⟨w, Algebra.smul_def f w⟩
      simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [map_add, show (Ideal.Quotient.mk I) (f • w) = 0 from
        (Ideal.Quotient.eq_zero_iff_mem).2 hfw, add_zero]
    rw [htop]
    exact (Module.Finite.iff_fg.1 (finite_smulMemRange hfB n₀)).map _
  -- Its spectrum has closed image in `Spec A`, which must contain the closed point.
  obtain ⟨q, hle⟩ := exists_primeSpectrum_map_maximalIdeal_le (A := A) (C := B ⧸ I)
  rw [IsScalarTower.algebraMap_eq A B (B ⧸ I), ← Ideal.map_map, hmB, Ideal.map_top] at hle
  exact q.isPrime.ne_top (top_le_iff.1 hle)

end Stacks.Divisors
