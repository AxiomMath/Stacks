module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Rings over which every finite flat module is finite locally free

Let `R` be a commutative ring. This file proves that every closed subset of `Spec(R)` which is
stable under generalization is open if and only if every finite flat `R`-module is projective.

For the forward implication, the rank function `𝔭 ↦ rank_{R_𝔭} M_𝔭` of a finite flat module `M` is
upper semicontinuous — Nakayama produces, near `𝔭`, a surjection from a free module of rank
`rank M_𝔭` onto `M` — and it is constant along inclusions of primes. So each set
`{𝔭 : n ≤ rank M_𝔭}` is closed and stable under generalization, hence open by the hypothesis, and
the rank function is locally constant. On a standard open where the rank is constant, `M` becomes
free after a further localization, so `M` is finitely presented, and a finitely presented flat
module is projective.

For the converse, a closed subset stable under generalization is the vanishing locus of a *pure*
ideal: writing `Z = V(J)` with `J` radical, the ideal `I = {x : ∃ f ∈ J, x * f = x}` satisfies
`V(I) = V(J)` and `x ∈ I → ∃ y ∈ I, x * y = x`. Purity says exactly that `R ⧸ I` is the
localization of `R` at the multiplicative set `1 + I`, hence flat over `R`; it is finite, so the
hypothesis makes it projective, and the rank of a finite projective module is locally constant, so
its support `V(I) = Z` is open.

## Main results

* `Stacks.LocallyFree.FiniteFlatCriterion.solution`: the two conditions above are equivalent.

## Implementation notes

The exterior powers of the source's argument are replaced by upper semicontinuity of the rank:
`{𝔭 : n ≤ rank M_𝔭}` is the support of `∧ⁿ M` in the source, and its closedness is obtained here
from Nakayama directly, which avoids having to know that exterior powers of a finite flat module
are finite and flat. The final descent step is likewise done by localizing twice rather than by
exhibiting a basis, using `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`.

## References

* [Stacks Project, Tag 052U](https://stacks.math.columbia.edu/tag/052U)
-/



namespace Stacks.LocallyFree.FiniteFlatCriterion

open Module PrimeSpectrum

attribute [local instance] Module.free_of_flat_of_isLocalRing

section

variable {R : Type u} [CommRing R]

/-! ### Upper semicontinuity of the rank of a finite flat module -/

/-- The rank of a finite flat module is upper semicontinuous on the spectrum: this is Nakayama's
lemma, in the form that a basis of `M_𝔭` is defined over a standard open neighbourhood of `𝔭` and
generates `M` there. -/
private lemma isOpen_rankAtStalk_le (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (n : ℕ) :
    IsOpen {q : PrimeSpectrum R | rankAtStalk M q ≤ n} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  let k := rankAtStalk M p
  let f : (Fin k →₀ R) →ₗ[R] Fin k →₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
  let g : M →ₗ[R] Mₚ := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  obtain ⟨φ, -, -, hφps⟩ := Module.exists_localizedMap_surjective_of_surjective
    p.asIdeal.primeCompl f g ((Module.finBasis Rₚ Mₚ).repr.restrictScalars R).symm.surjective
  rw [IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective f g] at hφps
  obtain ⟨a, hap, hφas⟩ :=
    Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p.asIdeal φ hφps
  refine ⟨(basicOpen a : Set (PrimeSpectrum R)), ?_, (basicOpen a).2, by simpa using hap⟩
  intro q hq
  rw [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker,
    LocalizedModule.subsingleton_iff_support_subset] at hφas
  have hqa : a ∉ q.asIdeal := by simpa [PrimeSpectrum.mem_basicOpen] using hq
  have hqs : q ∉ Module.support R (M ⧸ φ.range) := fun h => hqa (hφas h rfl)
  rw [Module.notMem_support_iff] at hqs
  have hsurj : Function.Surjective (LocalizedModule.map q.asIdeal.primeCompl φ) := by
    rwa [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
  show rankAtStalk M q ≤ n
  have : Nontrivial R := ⟨1, 0, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩
  calc rankAtStalk M q
      = Module.finrank (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := rfl
    _ ≤ Module.finrank (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl (Fin k →₀ R)) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = rankAtStalk (R := R) (Fin k →₀ R) q := rfl
    _ = k := by simp
    _ ≤ n := hp

/-! ### Two local criteria -/

/-- Finite presentation is local on the spectrum: it suffices that every maximal ideal be avoided
by some `a` such that the localization away from `a` is finitely presented. -/
private lemma finitePresentation_of_forall_maximal {A : Type w} [CommRing A] (N : Type v)
    [AddCommGroup N] [Module A N]
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ a ∉ P,
      Module.FinitePresentation (Localization.Away a) (LocalizedModule.Away a N)) :
    Module.FinitePresentation A N := by
  refine Module.FinitePresentation.of_localizationSpan
    {a : A | Module.FinitePresentation (Localization.Away a) (LocalizedModule.Away a N)} ?_
    fun g => g.2
  by_contra hs
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hs
  obtain ⟨a, haP, ha⟩ := h P hP
  exact haP (hle (Ideal.subset_span ha))

/-- If the rank of a finite flat module `M` is constant on a standard open `D(f)`, then `M` is
finitely presented over `R_f`. -/
private lemma finitePresentation_away_of_rankAtStalk_eq (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] {f : R} {k : ℕ}
    (hf : ∀ q ∈ (basicOpen f : Set (PrimeSpectrum R)), rankAtStalk M q = k) :
    Module.FinitePresentation (Localization.Away f) (LocalizedModule.Away f M) := by
  have hrank : ∀ Q : PrimeSpectrum (Localization.Away f),
      rankAtStalk (LocalizedModule.Away f M) Q = k := by
    intro Q
    rw [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers f) M) Q]
    refine hf _ ?_
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact ⟨Q, rfl⟩
  refine finitePresentation_of_forall_maximal _ fun P hP => ?_
  have := hP
  have := hP.isPrime
  obtain ⟨a, haP, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant
    (LocalizedModule.Away f M) P fun m _ => by
      rw [hrank ⟨m, inferInstance⟩, hrank ⟨P, inferInstance⟩]
  exact ⟨a, haP, Module.finitePresentation_of_projective _ _⟩

/-! ### (1) implies (2) -/

/-- If every closed subset of `Spec(R)` stable under generalization is open, then every finite flat
`R`-module is projective. -/
@[sga "1 IV 4.3" "case (b): (iii) ⇒ (ii)"]
private lemma projective_of_forall_isOpen
    (h : ∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.Projective R M := by
  have hge : ∀ n : ℕ, IsOpen {q : PrimeSpectrum R | n ≤ rankAtStalk M q} := by
    intro n
    match n with
    | 0 => simp
    | (m + 1) =>
      refine h _ ?_ ?_
      · have he : {q : PrimeSpectrum R | m + 1 ≤ rankAtStalk M q}
            = ({q : PrimeSpectrum R | rankAtStalk M q ≤ m}ᶜ : Set (PrimeSpectrum R)) := by
          ext q
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
          omega
        rw [he, isClosed_compl_iff]
        exact isOpen_rankAtStalk_le M m
      · intro x y hyx hx
        have hle : y ≤ x := (PrimeSpectrum.le_iff_specializes y x).2 hyx
        simpa [rankAtStalk_eq_of_le_of_finite_of_flat M hle] using hx
  have hfp : Module.FinitePresentation R M := by
    refine finitePresentation_of_forall_maximal M fun P hP => ?_
    have := hP.isPrime
    set p : PrimeSpectrum R := ⟨P, inferInstance⟩
    set A : Set (PrimeSpectrum R) := {q | rankAtStalk M q = rankAtStalk M p}
    have hpA : p ∈ A := rfl
    have hopen : IsOpen A := by
      have he : A = {q : PrimeSpectrum R | rankAtStalk M p ≤ rankAtStalk M q}
          ∩ {q : PrimeSpectrum R | rankAtStalk M q ≤ rankAtStalk M p} := by
        ext q
        exact ⟨fun hq => ⟨hq.ge, hq.le⟩, fun hq => le_antisymm hq.2 hq.1⟩
      rw [he]
      exact (hge _).inter (isOpen_rankAtStalk_le M _)
    obtain ⟨V, ⟨b, rfl⟩, hpV, hVsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpA hopen
    exact ⟨b, by simpa using hpV,
      finitePresentation_away_of_rankAtStalk_eq M fun q hq => hVsub hq⟩
  exact Module.Flat.projective_of_finitePresentation

/-! ### The pure core of an ideal -/

/-- The *pure core* of an ideal `J` of `R`: the set of `x : R` with `x * f = x` for some `f ∈ J`.
It is the largest pure ideal with the same vanishing locus as `J`, when `V(J)` is stable under
generalization. -/
private def pureCore (J : Ideal R) : Ideal R where
  carrier := {x | ∃ f ∈ J, x * f = x}
  add_mem' := by
    rintro x y ⟨f, hf, hx⟩ ⟨g, hg, hy⟩
    exact ⟨f + g - f * g, sub_mem (add_mem hf hg) (J.mul_mem_left f hg), by
      linear_combination (1 - g) * hx + (1 - f) * hy⟩
  zero_mem' := ⟨0, J.zero_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨f, hf, hx⟩
    exact ⟨f, hf, by rw [smul_eq_mul, mul_assoc, hx]⟩

private lemma pureCore_le (J : Ideal R) : pureCore J ≤ J := by
  rintro x ⟨f, hf, hx⟩
  rw [← hx]
  exact J.mul_mem_left x hf

/-- If `x * y = x` then `x * yⁿ = x`. -/
private lemma mul_pow_eq_self {x y : R} (h : x * y = x) : ∀ n : ℕ, x * y ^ n = x
  | 0 => by simp
  | n + 1 => by rw [pow_succ, ← mul_assoc, mul_pow_eq_self h n, h]

/-- The pure core of `J` has the same vanishing locus as `J`, provided `V(J)` is stable under
generalization. -/
private lemma zeroLocus_pureCore (J : Ideal R)
    (hJ : StableUnderGeneralization (zeroLocus (J : Set R))) :
    zeroLocus ((pureCore J : Ideal R) : Set R) = zeroLocus (J : Set R) := by
  refine le_antisymm ?_ (zeroLocus_anti_mono_ideal (pureCore_le J))
  intro p hp
  rw [mem_zeroLocus] at hp ⊢
  let S : Submonoid R :=
    { carrier := {x | ∃ u ∉ p.asIdeal, ∃ f ∈ J, x = u * (1 + f)}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨u, hu, f, hf, rfl⟩ := hx
        obtain ⟨v, hv, g, hg, rfl⟩ := hy
        exact ⟨u * v, fun hm => (p.isPrime.mem_or_mem hm).elim hu hv,
          f + g + f * g, add_mem (add_mem hf hg) (J.mul_mem_left f hg), by ring⟩
      one_mem' := ⟨1, p.isPrime.one_notMem, 0, J.zero_mem, by ring⟩ }
  have h0 : (0 : R) ∉ S := by
    rintro ⟨u, hu, f, hf, h0⟩
    exact hu (hp (show u ∈ pureCore J from ⟨-f, neg_mem hf, by linear_combination h0⟩))
  obtain ⟨q, hq, -, hqS⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) S
    (by simpa [Set.disjoint_left] using h0)
  have hqp : q ≤ p.asIdeal := by
    intro x hx
    by_contra hxp
    exact Set.disjoint_left.1 hqS hx ⟨x, hxp, 0, J.zero_mem, by ring⟩
  have hne : q ⊔ J ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ q ⊔ J := htop ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨a, ha, f, hf, haf⟩ := h1
    exact Set.disjoint_left.1 hqS ha
      ⟨1, p.isPrime.one_notMem, -f, neg_mem hf, by linear_combination haf⟩
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmZ : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ zeroLocus (J : Set R) :=
    (mem_zeroLocus _ _).2 fun x hx => (le_sup_right.trans hle : J ≤ m) hx
  have hqZ : (⟨q, hq⟩ : PrimeSpectrum R) ∈ zeroLocus (J : Set R) :=
    hJ ((PrimeSpectrum.le_iff_specializes (⟨q, hq⟩ : PrimeSpectrum R) ⟨m, hm.isPrime⟩).1
      (le_sup_left.trans hle)) hmZ
  exact fun x hx => hqp ((mem_zeroLocus _ _).1 hqZ hx)

/-- The pure core of `J` is a pure ideal: `x ∈ I` implies `x * y = x` for some `y ∈ I`. -/
private lemma pureCore_isPure (J : Ideal R)
    (h : zeroLocus ((pureCore J : Ideal R) : Set R) = zeroLocus (J : Set R)) :
    ∀ x ∈ pureCore J, ∃ y ∈ pureCore J, x * y = x := by
  have hrad : (pureCore J).radical = J.radical := PrimeSpectrum.zeroLocus_eq_iff.1 h
  rintro x ⟨f, hf, hx⟩
  obtain ⟨n, hn⟩ : f ∈ (pureCore J).radical := by
    rw [hrad]
    exact Ideal.le_radical hf
  exact ⟨f ^ n, hn, mul_pow_eq_self hx n⟩

/-- A pure ideal `I` makes `R ⧸ I` the localization of `R` at `1 + I`, hence flat. -/
private lemma flat_quotient_of_isPure (I : Ideal R)
    (hI : ∀ x ∈ I, ∃ y ∈ I, x * y = x) : Module.Flat R (R ⧸ I) := by
  let S : Submonoid R :=
    { carrier := {x | x - 1 ∈ I}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        show a * b - 1 ∈ I
        rw [show a * b - 1 = (a - 1) * b + (b - 1) by ring]
        exact I.add_mem (I.mul_mem_right b ha) hb }
  have : IsLocalization S (R ⧸ I) := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
    · have hy : (algebraMap R (R ⧸ I)) (y : R) = 1 := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).2 y.2
      exact hy ▸ isUnit_one
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨⟨a, 1⟩, by simp⟩
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hxy
      obtain ⟨t, ht, hxt⟩ := hI _ hxy
      have hmem : (1 - t) ∈ S := by
        show (1 : R) - t - 1 ∈ I
        simpa using neg_mem ht
      refine ⟨⟨1 - t, hmem⟩, ?_⟩
      show (1 - t) * x = (1 - t) * y
      linear_combination -hxt
  exact IsLocalization.flat (R ⧸ I) S

/-- The support of a finite projective module is open, since its rank is locally constant. -/
@[sga "3 VIA 2.1.3" "special case"]
private lemma isOpen_support (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] [Module.Projective R M] : IsOpen (Module.support R M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have he : Module.support R M = rankAtStalk M ⁻¹' {n : ℕ | n ≠ 0} := by
    ext q
    simp [← rankAtStalk_pos_iff_mem_support, Nat.pos_iff_ne_zero]
  rw [he]
  exact Module.isLocallyConstant_rankAtStalk (M := M) _

/-! ### (2) implies (1) -/

/-- If every finite flat `R`-module is projective, then every closed subset of `Spec(R)` stable
under generalization is open. -/
private lemma isOpen_of_forall_projective
    (h : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
      Module.Projective R M)
    (Z : Set (PrimeSpectrum R)) (hZc : IsClosed Z) (hZg : StableUnderGeneralization Z) :
    IsOpen Z := by
  set J : Ideal R := vanishingIdeal Z with hJdef
  have hZ : zeroLocus (J : Set R) = Z := by
    rw [hJdef, zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  have hIJ : zeroLocus ((pureCore J : Ideal R) : Set R) = zeroLocus (J : Set R) :=
    zeroLocus_pureCore J (by rwa [hZ])
  have : Module.Flat R (R ⧸ pureCore J) :=
    flat_quotient_of_isPure _ (pureCore_isPure J hIJ)
  have : Module.Projective R (R ⧸ pureCore J) := h (R ⧸ pureCore J)
  have hop := isOpen_support (R := R) (R ⧸ pureCore J)
  rwa [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, hIJ, hZ] at hop

end

/-! ### The equivalence -/

/-- Every closed subset of `Spec R` that is stable under generalization is open if and only if
every finite flat `R`-module is projective. -/
public theorem solution (R : Type u) [CommRing R] :
    (∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
        Module.Projective R M :=
  ⟨fun h M _ _ _ _ => projective_of_forall_isOpen h M, isOpen_of_forall_projective⟩

end Stacks.LocallyFree.FiniteFlatCriterion

/-!
# Rings over which every finite flat module is finite locally free

Let `R` be a commutative ring. A finite flat `R`-module `M` is free at every prime, and its
support is closed and stable under generalization, but `M` need not be finite locally free: that
fails exactly when some closed generalization-stable subset of `Spec(R)` is not open. This file
records the equivalence of the two conditions:

1. every `Z ⊆ Spec(R)` which is closed and stable under generalization is open;
2. every finite flat `R`-module is finite locally free.

The mechanism, for orientation. For (2) `⇒` (1), a closed generalization-stable `Z` is `V(I)` for
a pure ideal `I`, and `R/I` is then a finite flat module whose support is `Z`, so (2) makes `Z`
open. For (1) `⇒` (2), the support of a finite flat `M` is closed and stable under generalization
because `M_𝔭 = M_{𝔭'} ⊗_{R_{𝔭'}} R_𝔭` for `𝔭 ⊆ 𝔭'`; applying (1) to the supports of the exterior
powers `∧ⁱM` decomposes `Spec(R)` into open and closed pieces on which `M` has constant rank, and
Nakayama produces a basis on each.

## Main results

* `PrimeSpectrum.forall_isOpen_of_isClosed_of_stableUnderGeneralization_iff_forall_projective`:
  the two conditions above are equivalent.

## Implementation notes

The source's items are the two sides of the `Iff`, in the source's order: the topological condition
is the left-hand side.

*Finite locally free* is spelled `Module.Projective R M` for a module already hypothesised finite.
The source's covering form — `Spec(R)` covered by standard opens `D(f)` with each `M_f` finite
free over `R_f` — is item (7) of Stacks 00NX, and `Module.finite_projective_tfae` in this library
proves it equivalent to item (2), "`M` is finite projective". The abstract form is taken because it
is the one Mathlib's API is phrased in and the one that composes; nothing is lost, and a user who
wants the covering reads it off that equivalence.

Stability under generalization is Mathlib's `StableUnderGeneralization`, i.e. `y ⤳ x` and `x ∈ Z`
imply `y ∈ Z`. On `PrimeSpectrum R` specialization is inclusion of primes
(`PrimeSpectrum.le_iff_specializes`), so this unfolds to the source's phrasing: `𝔭 ⊆ 𝔭'` and
`𝔭' ∈ Z` imply `𝔭 ∈ Z`.

Finiteness and flatness of the test module are instance binders rather than hypotheses of an
implication, so that an application `h M` synthesises them from the context.

The test modules of (2) are quantified in the universe of `R`, as Mathlib does in
`Module.flat_iff`. This is not a restriction: a finite `R`-module is a quotient of `Fin n → R`,
hence isomorphic to a module in `Type u`, and finiteness, flatness and projectivity all transport
along a `LinearEquiv`. Quantifying instead over an arbitrary universe `v` unrelated to `u` would
make the statement false rather than more general, since (2) would then say nothing about the
modules `R/I` used to prove (1) — a smallness hypothesis `Small.{v} R` would be needed to restore
it, and it would buy nothing.

Faithfulness. (1) No hypothesis is dead: `R` carries only `CommRing`, and inside the two conditions
each conjunct is used — over `ℤ`, which satisfies (1), the set `{(0)}` is stable under
generalization but neither closed nor open, and `{(2)}` is closed but not open, so neither
`IsClosed` nor `StableUnderGeneralization` may be dropped from (1); likewise `ℚ` over `ℤ` is flat
and not projective, and `ZMod 2` over `ℤ` is finite and not projective, so neither `Module.Finite`
nor `Module.Flat` may be dropped from (2). (2) The scalars are the source's: `Spec(R)` is
`PrimeSpectrum R`, and flatness and projectivity are over `R` itself, no localization occurring in
the statement. (3) The source names no canonical map here, both items being properties of `R`; the
one phrase that needed pinning, "finite locally free", is pinned to a named equivalence rather than
left to the reader, as described above. (4) The instantiation is not degenerate: every Noetherian
ring satisfies (2), since for it `Module.Finite` is `Module.FinitePresentation`
(`Module.finitePresentation_iff_finite`) and `Module.Flat.projective_of_finitePresentation`
applies, so `R = ℤ` witnesses both sides; and both sides fail for `R = ∀ n : ℕ, ZMod 2`, where the
finitely supported sequences form a pure ideal `I` that is not finitely generated, making `R/I`
finite and flat but not finitely presented, hence not projective.

## References

* [Stacks Project, Tag 052U](https://stacks.math.columbia.edu/tag/052U)

## Tags

finite flat module, finite locally free, pure ideal, prime spectrum, generalization

-/



namespace PrimeSpectrum

/-- Let `R` be a commutative ring. Every closed subset of `Spec(R)` that is stable under
generalization is open if and only if every finite flat `R`-module is finite locally free, the
latter being spelled "finite projective" (Stacks 00NX (2) `⇔` (7)). -/
@[stacks 052U "Finite local freeness is spelled `Module.Projective`; see the module docstring."]
public theorem forall_isOpen_of_isClosed_of_stableUnderGeneralization_iff_forall_projective
    (R : Type u) [CommRing R] :
    (∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
        Module.Projective R M :=
  Stacks.LocallyFree.FiniteFlatCriterion.solution R

end PrimeSpectrum
