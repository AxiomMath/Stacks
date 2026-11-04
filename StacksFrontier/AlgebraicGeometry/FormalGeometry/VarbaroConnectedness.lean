module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalLocusConnected
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.Dualizing.Depth
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Sum
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Varbaro's connectedness theorem: Stacks 0ECR

Let `(A, 𝔪)` be a Noetherian complete local ring and `I ⊆ A` a proper ideal, and put
`X = Spec(A)` and `Y = V(I)`. Denote by `d` the minimal dimension of an irreducible component of
`X` and by `c` the minimal dimension of a closed subset `Z ⊆ X` whose complement `X ∖ Z` is
disconnected. Stacks 0ECR (Varbaro, Theorem 1.6) says that for a closed `Z ⊆ Y` the complement
`Y ∖ Z` is connected as soon as `dim(Z) < min(c, d - 1) - cd(A, I)`, and in particular that the
punctured spectrum of `A/I` is connected if `cd(A, I) < min(c, d - 1)`. This file proves both.

## Main definitions

* `Stacks.Algebraization.minDimIrreducibleComponent` — the number `d`: the least dimension of an
  irreducible component.
* `Stacks.Algebraization.minDimDisconnectingClosed` — the number `c`: the least dimension of a
  closed subset with disconnected complement.

## Main results

* `Stacks.Algebraization.exists_irreducibleComponent_topologicalKrullDim_eq_minDim` and
  `Stacks.Algebraization.exists_isClosed_not_isConnected_compl_topologicalKrullDim_eq_minDim` —
  for the spectrum of a Noetherian local ring both minima are attained, so the two numbers are
  the minima of the source.
* `Stacks.Algebraization.isConnected_zeroLocus_diff_closedPoint_of_cohomologicalDimension_lt` —
  the final assertion, read in `Spec(A)`: `V(I) ∖ {𝔪}` is connected.
* `Stacks.Algebraization.isConnected_zeroLocus_diff_of_krullDimToEInt_lt` — the main assertion.
* `Stacks.Algebraization.isConnected_zeroLocus_diff_and_isConnected_puncturedSpectrum_quotient`
  — **Stacks 0ECR**, both assertions, the second for the punctured spectrum of `A/I` itself.

## The proof

The final assertion is Stacks 0EG5 (`eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex`)
at `𝔞 = 𝔪`: the complete local ring `A` has a dualizing complex (Stacks 0BFR) and is `I`-adically
complete (Stacks 090T). The dimension condition of Stacks 0EG5 is `d - 1 > cd(A, I)`.
Its connectedness hypothesis holds because a disconnected open `V ⊇ V(I) ∖ {𝔪}` has a complement
`Z` meeting `V(I)` at most in `𝔪`, whose dimension is at most `cd(A, I)` by Stacks 0DXF, so that
`c ≤ cd(A, I)`. If `V(I) ∖ {𝔪}` were empty, Stacks 0DXF would give `d ≤ cd(A, I)`.

For the main assertion, let `Y ∖ Z` be disconnected with `dim(Z) = e`. Either `Y ∖ Z` is empty,
or it splits into two nonempty relatively open pieces, in each of which we pick a point closed in
the punctured spectrum (a Jacobson space, Stacks 02IM). By prime avoidance we choose
`f₁, …, f_e ∈ 𝔪`, all vanishing at the two chosen points, with each `fᵢ` outside every minimal
prime of the previous cut, so that the dimension drops by one at each step and
`V(f₁, …, f_e) ∩ Z = {𝔪}`. Then the punctured spectrum of `A/(I + (f₁, …, f_e))` is disconnected,
and `cd(A, I + (f₁, …, f_e)) ≤ cd(A, I) + e` (Stacks 0ECP and 0DX9), so the final assertion
gives `cd(A, I) + e ≥ min(c, d - 1)`.

## Implementation notes

The minima `c` and `d` are natural numbers, taken as the infimum in `ℕ` of the dimensions that
occur; the attainment lemmas show they are the minima. Dimensions of closed subsets are
`topologicalKrullDim` (with `dim ∅ = ⊥`), compared with the integer `min(c, d - 1) - cd(A, I)`
through `krullDimToEInt`, so the strict inequality for `Z = ∅` holds for every integer, as in
the source.

## References

* [Stacks Project, Tag 0ECR](https://stacks.math.columbia.edu/tag/0ECR)
* M. Varbaro, *Cohomological and projective dimensions*, Theorem 1.6.
-/

@[expose] public noncomputable section

open IsLocalRing PrimeSpectrum TopologicalSpace Topology

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- The minimal dimension of an irreducible component of a topological space `X`, the number
`d` of Stacks 0ECR. It is the least natural number which is the dimension of an irreducible
component; for the spectrum of a Noetherian local ring it is attained, see
`exists_irreducibleComponent_topologicalKrullDim_eq_minDim`. -/
def minDimIrreducibleComponent (X : Type*) [TopologicalSpace X] : ℕ :=
  sInf {n : ℕ | ∃ C ∈ irreducibleComponents X, topologicalKrullDim C = n}

/-- The minimal dimension of a closed subset `Z` of a topological space `X` such that `X ∖ Z` is
disconnected, the number `c` of Stacks 0ECR. It is the least natural number which is the
dimension of such a `Z`; for the spectrum of a Noetherian local ring it is attained, see
`exists_isClosed_not_isConnected_compl_topologicalKrullDim_eq_minDim`. -/
def minDimDisconnectingClosed (X : Type*) [TopologicalSpace X] : ℕ :=
  sInf {n : ℕ | ∃ Z : Set X, IsClosed Z ∧ ¬ IsConnected Zᶜ ∧ topologicalKrullDim Z = n}

section Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- A proper quotient of a Noetherian local ring has finite Krull dimension. -/
theorem exists_ringKrullDim_quotient_eq_natCast (J : Ideal A) (hJ : J ≠ ⊤) :
    ∃ n : ℕ, ringKrullDim (A ⧸ J) = n := by
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hlt : ringKrullDim (A ⧸ J) < ⊤ :=
    (ringKrullDim_quotient_le J).trans_lt ringKrullDim_lt_top
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp
    (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
      (ringKrullDim_nonneg_of_nontrivial (R := A ⧸ J))).ne'
  have hy' : y ≠ ⊤ := by
    rintro rfl
    rw [← hy] at hlt
    exact lt_irrefl _ (hlt.trans_le le_top)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hy'
  exact ⟨n, hy.symm⟩

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The dimension of a closed subset of `Spec(A)` is the Krull dimension of the quotient by its
vanishing ideal. -/
@[ega "IV 5.1.1" "special case"]
theorem topologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal
    {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z) :
    topologicalKrullDim Z = ringKrullDim (A ⧸ vanishingIdeal Z) := by
  have h := Stacks.Spectrum.LocalDimensionFormula.topologicalKrullDim_zeroLocus (vanishingIdeal Z)
  rwa [zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at h

omit [IsNoetherianRing A] in
/-- A closed subset of `Spec(A)` which is nonempty contains the closed point. -/
theorem closedPoint_mem_of_isClosed {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (hne : Z.Nonempty) : closedPoint A ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  exact ((le_iff_specializes z (closedPoint A)).mp le_top).mem_closed hZ hz

omit [IsNoetherianRing A] in
/-- The zero locus of a proper ideal of a local ring is connected: it contains the closed point,
which lies in the closure of each of its points. -/
theorem isConnected_zeroLocus (J : Ideal A) (hJ : J ≠ ⊤) :
    IsConnected (zeroLocus (J : Set A)) := by
  refine ⟨⟨closedPoint A, closedPoint_mem_zeroLocus hJ⟩,
    isPreconnected_of_forall (closedPoint A) fun y hy => ?_⟩
  refine ⟨closure {y}, closure_minimal (Set.singleton_subset_iff.mpr hy)
    (isClosed_zeroLocus _), ?_, subset_closure rfl, isPreconnected_singleton.closure⟩
  exact (le_iff_mem_closure y (closedPoint A)).mp le_top

/-- **Stacks 0DXF for a closed subset.** If a closed subset `V(J)` of `Spec(A)` meets `V(I)` at
most in the closed point, then `dim(A/J) ≤ cd(A, I)`. The dimension is attained along a chain
starting at a minimal prime `𝔮` of `J`, and Stacks 0DXF bounds `dim(A/𝔮)`. -/
theorem natCast_le_cohomologicalDimension_of_zeroLocus_inter_subset (I J : Ideal A)
    (hI : I ≠ ⊤)
    (hJI : zeroLocus (J : Set A) ∩ zeroLocus (I : Set A) ⊆ {closedPoint A})
    (n : ℕ) (hn : ringKrullDim (A ⧸ J) = n) :
    (n : ℤ) ≤ cohomologicalDimension A I I.fg_of_isNoetherianRing := by
  have hdimJ : (n : WithBot ℕ∞) ≤ Order.krullDim (zeroLocus (J : Set A)) := by
    rw [← Order.krullDim_eq_of_orderIso J.primeSpectrumQuotientOrderIsoZeroLocus]
    exact hn.symm.le
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hdimJ
  have hhead : J ≤ l.head.1.asIdeal := (mem_zeroLocus _ _).mp l.head.2
  obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le hhead
  have : q.IsPrime := hqmin.1.1
  let Q : PrimeSpectrum A := ⟨q, hqmin.1.1⟩
  let l' : LTSeries (PrimeSpectrum A) := l.map Subtype.val (fun _ _ h => h)
  have hlen : (n : ℕ∞) ≤ Order.coheight Q := by
    have := Order.length_le_coheight (p := l') (x := Q) hqle
    have h1 : l'.length = n := hl
    rwa [h1] at this
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq_natCast q hqmin.1.1.ne_top
  have hmQ : Order.coheight Q = (m : ℕ∞) := by
    have := (coheight_eq_ringKrullDim_quotient Q).trans hm
    exact_mod_cast this
  have hnm : n ≤ m := by
    rw [hmQ] at hlen
    exact_mod_cast hlen
  have hinter : zeroLocus (q : Set A) ∩ zeroLocus (I : Set A) = {closedPoint A} := by
    refine Set.Subset.antisymm (fun x hx => hJI ⟨?_, hx.2⟩) ?_
    · exact zeroLocus_anti_mono_ideal hqmin.1.2 hx.1
    · rw [Set.singleton_subset_iff]
      exact ⟨closedPoint_mem_zeroLocus hqmin.1.1.ne_top, closedPoint_mem_zeroLocus hI⟩
  have h0DXF := ringKrullDim_quotient_le_cohomologicalDimension' A q I
    I.fg_of_isNoetherianRing hinter m hm
  omega

/-- If the complement of `Z` is not connected, then `Z` is nonempty. -/
private theorem nonempty_of_not_isConnected_compl {R : Type*} [CommRing R] [IsLocalRing R]
    {Z : Set (PrimeSpectrum R)} (h : ¬ IsConnected Zᶜ) : Z.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [Set.compl_empty, ← zeroLocus_bot] at h
  exact h (isConnected_zeroLocus ⊥ bot_ne_top)

/-- A nonempty closed subset of `Spec(A)` has natural number dimension, which is the dimension of
the quotient by its vanishing ideal. -/
private theorem exists_dim_eq_natCast_of_isClosed {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (hne : Z.Nonempty) :
    ∃ n : ℕ, ringKrullDim (A ⧸ vanishingIdeal Z) = n ∧ topologicalKrullDim Z = n := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_quotient_eq_natCast _
    (fun h => hne.ne_empty (vanishingIdeal_eq_top_iff.mp h))
  exact ⟨n, hn, (topologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal hZ).trans hn⟩

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The least dimension of an irreducible component is at most the dimension of `A/𝔭` for every
minimal prime `𝔭`. -/
theorem minDimIrreducibleComponent_le {p : Ideal A} (hp : p ∈ minimalPrimes A) (n : ℕ)
    (hn : ringKrullDim (A ⧸ p) = n) :
    minDimIrreducibleComponent (PrimeSpectrum A) ≤ n := by
  refine Nat.sInf_le ⟨zeroLocus (p : Set A), ?_, ?_⟩
  · rw [← zeroLocus_minimalPrimes]
    exact ⟨p, hp, rfl⟩
  · rw [Stacks.Spectrum.LocalDimensionFormula.topologicalKrullDim_zeroLocus p, hn]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The least dimension of a closed subset with disconnected complement is at most the dimension
of each such subset. -/
theorem minDimDisconnectingClosed_le {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (hZc : ¬ IsConnected Zᶜ) (n : ℕ) (hn : topologicalKrullDim Z = n) :
    minDimDisconnectingClosed (PrimeSpectrum A) ≤ n :=
  Nat.sInf_le ⟨Z, hZ, hZc, hn⟩

/-- The minimum `d` of Stacks 0ECR is attained: some irreducible component of `Spec(A)` has
dimension `d`, and every irreducible component has dimension at least `d`. -/
theorem exists_irreducibleComponent_topologicalKrullDim_eq_minDim :
    (∃ C ∈ irreducibleComponents (PrimeSpectrum A),
      topologicalKrullDim C = minDimIrreducibleComponent (PrimeSpectrum A)) ∧
    ∀ C ∈ irreducibleComponents (PrimeSpectrum A),
      (minDimIrreducibleComponent (PrimeSpectrum A) : WithBot ℕ∞) ≤ topologicalKrullDim C := by
  have hcomp : ∀ C ∈ irreducibleComponents (PrimeSpectrum A),
      ∃ n : ℕ, topologicalKrullDim C = n := by
    intro C hC
    rw [← zeroLocus_minimalPrimes] at hC
    obtain ⟨p, hp, rfl⟩ := hC
    obtain ⟨n, hn⟩ := exists_ringKrullDim_quotient_eq_natCast p hp.1.1.ne_top
    exact ⟨n, by
      simp only [Function.comp_apply]
      rw [Stacks.Spectrum.LocalDimensionFormula.topologicalKrullDim_zeroLocus p, hn]⟩
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ maximalIdeal A)
  have hpC : zeroLocus (p : Set A) ∈ irreducibleComponents (PrimeSpectrum A) := by
    rw [← zeroLocus_minimalPrimes]
    exact ⟨p, hp, rfl⟩
  have hne : {n : ℕ | ∃ C ∈ irreducibleComponents (PrimeSpectrum A),
      topologicalKrullDim C = n}.Nonempty := by
    obtain ⟨n, hn⟩ := hcomp _ hpC
    exact ⟨n, _, hpC, hn⟩
  refine ⟨Nat.sInf_mem hne, fun C hC => ?_⟩
  obtain ⟨n, hn⟩ := hcomp C hC
  rw [hn]
  exact_mod_cast (Nat.sInf_le ⟨C, hC, hn⟩ : minDimIrreducibleComponent (PrimeSpectrum A) ≤ n)

/-- The minimum `c` of Stacks 0ECR is attained: some closed subset of `Spec(A)` with disconnected
complement has dimension `c`, and every such subset has dimension at least `c`. -/
theorem exists_isClosed_not_isConnected_compl_topologicalKrullDim_eq_minDim :
    (∃ Z : Set (PrimeSpectrum A), IsClosed Z ∧ ¬ IsConnected Zᶜ ∧
      topologicalKrullDim Z = minDimDisconnectingClosed (PrimeSpectrum A)) ∧
    ∀ Z : Set (PrimeSpectrum A), IsClosed Z → ¬ IsConnected Zᶜ →
      (minDimDisconnectingClosed (PrimeSpectrum A) : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hfin : ∀ Z : Set (PrimeSpectrum A), IsClosed Z → ¬ IsConnected Zᶜ →
      ∃ n : ℕ, topologicalKrullDim Z = n := by
    intro Z hZ hZc
    obtain ⟨n, -, hn⟩ := exists_dim_eq_natCast_of_isClosed hZ
      (nonempty_of_not_isConnected_compl hZc)
    exact ⟨n, hn⟩
  have huniv : ¬ IsConnected (Set.univ : Set (PrimeSpectrum A))ᶜ := by
    rw [Set.compl_univ]
    exact fun h => Set.not_nonempty_empty h.nonempty
  have hne : {n : ℕ | ∃ Z : Set (PrimeSpectrum A), IsClosed Z ∧ ¬ IsConnected Zᶜ ∧
      topologicalKrullDim Z = n}.Nonempty := by
    obtain ⟨n, hn⟩ := hfin _ isClosed_univ huniv
    exact ⟨n, _, isClosed_univ, huniv, hn⟩
  refine ⟨Nat.sInf_mem hne, fun Z hZ hZc => ?_⟩
  obtain ⟨n, hn⟩ := hfin Z hZ hZc
  rw [hn]
  exact_mod_cast minDimDisconnectingClosed_le hZ hZc n hn

/-- **Stacks 0ECR, the final assertion, in `Spec(A)`.** Let `(A, 𝔪)` be a Noetherian complete
local ring and `I` a proper ideal. If `cd(A, I) < c` and `cd(A, I) < d - 1`, then
`V(I) ∖ {𝔪}` is connected. -/
@[sga "2 XIII 2.1" "more general"]
theorem isConnected_zeroLocus_diff_closedPoint_of_cohomologicalDimension_lt
    [IsAdicComplete (maximalIdeal A) A] (I : Ideal A) (hI : I ≠ ⊤)
    (hc : cohomologicalDimension A I I.fg_of_isNoetherianRing <
      minDimDisconnectingClosed (PrimeSpectrum A))
    (hd : cohomologicalDimension A I I.fg_of_isNoetherianRing <
      (minDimIrreducibleComponent (PrimeSpectrum A) : ℤ) - 1) :
    IsConnected (zeroLocus (I : Set A) \ {closedPoint A}) := by
  have hIm : I ≤ maximalIdeal A := le_maximalIdeal hI
  have : IsAdicComplete I A :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete hIm inferInstance I.fg_of_isNoetherianRing
  set cd := cohomologicalDimension A I I.fg_of_isNoetherianRing with hcd
  have hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → maximalIdeal A ≤ q.asIdeal →
      ((cd + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) := by
    intro p q hp _ _ hmq
    have hq : q = closedPoint A :=
      PrimeSpectrum.ext (le_antisymm (le_maximalIdeal q.2.ne_top) hmq)
    rw [ringKrullDim_localization_quotient_map_of_eq_closedPoint hq]
    obtain ⟨n, hn⟩ := exists_ringKrullDim_quotient_eq_natCast p.asIdeal p.2.ne_top
    have hdn := minDimIrreducibleComponent_le hp n hn
    rw [hn, krullDimToEInt_natCast]
    exact WithBotTop.coe_lt_coe.mpr (by omega)
  have hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      zeroLocus (I : Set A) \ zeroLocus ((maximalIdeal A : Ideal A) : Set A) ⊆ V →
      IsConnected V := by
    intro V hV _ hTV
    by_contra hVc
    rw [zeroLocus_maximalIdeal] at hTV
    have hZ : IsClosed Vᶜ := hV.isClosed_compl
    have hVc' : ¬ IsConnected Vᶜᶜ := by rwa [compl_compl]
    obtain ⟨n, hn, hn'⟩ := exists_dim_eq_natCast_of_isClosed hZ
      (nonempty_of_not_isConnected_compl hVc')
    have hcn := minDimDisconnectingClosed_le hZ hVc' n hn'
    have hZeq : zeroLocus ((vanishingIdeal Vᶜ : Ideal A) : Set A) = Vᶜ := by
      rw [zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
    have hncd := natCast_le_cohomologicalDimension_of_zeroLocus_inter_subset I _ hI
      (by
        rw [hZeq]
        rintro x ⟨hxV, hxI⟩
        by_contra hxm
        exact hxV (hTV ⟨hxI, hxm⟩))
      n hn
    omega
  have h := eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex A I (maximalIdeal A)
    hIm (Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A) hdim hconn
  rw [zeroLocus_maximalIdeal] at h
  rcases h with h | h
  · exfalso
    have hYm : zeroLocus (I : Set A) ⊆ {closedPoint A} := by
      intro x hx
      by_contra hxm
      exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, hxm⟩
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ maximalIdeal A)
    obtain ⟨n, hn⟩ := exists_ringKrullDim_quotient_eq_natCast p hp.1.1.ne_top
    have h0DXF := natCast_le_cohomologicalDimension_of_zeroLocus_inter_subset I p hI
      (fun x hx => hYm hx.2) n hn
    have hdn := minDimIrreducibleComponent_le hp n hn
    omega
  · exact h

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- Cutting the dimension by one: if `x` lies outside every minimal prime of `J`, then
`dim(A/(J + (x))) + 1 ≤ dim(A/J)`. This is Mathlib's form of Stacks 0B52 for the module `A/J`. -/
theorem ringKrullDim_quotient_sup_span_singleton_add_one_le (J : Ideal A) {x : A}
    (hx : ∀ p ∈ J.minimalPrimes, x ∉ p) :
    ringKrullDim (A ⧸ (J ⊔ Ideal.span {x})) + 1 ≤ ringKrullDim (A ⧸ J) := by
  have h := Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes (R := A)
    (M := A ⧸ J) (x := x) (by rwa [Ideal.annihilator_quotient])
  rw [Module.supportDim_quotient_eq_ringKrullDim] at h
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  have hs : Module.support A (A ⧸ (J ⊔ Ideal.span {x})) =
      Module.support A (QuotSMulTop x (A ⧸ J)) := by
    rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient, Ideal.annihilator_quotient, zeroLocus_sup, zeroLocus_span]
  unfold Module.supportDim at h ⊢
  rwa [hs]

omit [IsLocalRing A] in
/-- One step of the choice of `f₁, …, f_e`: given an ideal `K` contained in no minimal prime of
`J`, prime avoidance gives `x ∈ K` cutting the dimension of `A/J` by one. -/
theorem exists_mem_ringKrullDim_quotient_sup_span_singleton_le (K J : Ideal A) (e : ℕ)
    (hJ : ringKrullDim (A ⧸ J) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hK : ∀ p ∈ J.minimalPrimes, ¬ K ≤ p) :
    ∃ x ∈ K, ringKrullDim (A ⧸ (J ⊔ Ideal.span {x})) ≤ (e : WithBot ℕ∞) := by
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A J
  have hnot : ¬ ((K : Set A) ⊆ ⋃ p ∈ (↑hfin.toFinset : Set (Ideal A)), (p : Set A)) := by
    rw [Ideal.subset_union_prime (f := fun p : Ideal A => p) ⊥ ⊥
      (fun p hp _ _ => ((Set.Finite.mem_toFinset hfin).mp hp).1.1)]
    rintro ⟨p, hp, hKp⟩
    exact hK p ((Set.Finite.mem_toFinset hfin).mp hp) hKp
  obtain ⟨x, hxK, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxK, ?_⟩
  have hx' : ∀ p ∈ J.minimalPrimes, x ∉ p := fun p hp hxp =>
    hx (Set.mem_iUnion₂.mpr ⟨p, (Set.Finite.mem_toFinset hfin).mpr hp, hxp⟩)
  have hdrop := (ringKrullDim_quotient_sup_span_singleton_add_one_le J hx').trans hJ
  generalize ringKrullDim (A ⧸ (J ⊔ Ideal.span {x})) = a at hdrop ⊢
  induction a with
  | bot => exact bot_le
  | coe b =>
    induction b with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [h1] at hdrop
      have h2 : (⊤ : ℕ∞) ≤ ((e + 1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hdrop
      exact absurd h2 (not_le.mpr (ENat.coe_lt_top _))
    | coe b =>
      have : b + 1 ≤ e + 1 := by exact_mod_cast hdrop
      exact_mod_cast (by omega : b ≤ e)

/-- **The choice of `f₁, …, f_e`.** If `dim(A/J) ≤ e` and an ideal `K` lies in no prime of
`V(J)` other than `𝔪`, there are `f₁, …, f_e ∈ K` with `V(J + (f₁, …, f_e)) ⊆ {𝔪}`. -/
theorem exists_fin_mem_zeroLocus_sup_span_subset_closedPoint (K : Ideal A) :
    ∀ (e : ℕ) (J : Ideal A), ringKrullDim (A ⧸ J) ≤ (e : WithBot ℕ∞) →
      (∀ q : PrimeSpectrum A, J ≤ q.asIdeal → q ≠ closedPoint A → ¬ K ≤ q.asIdeal) →
      ∃ f : Fin e → A, (∀ i, f i ∈ K) ∧
        zeroLocus ((J ⊔ Ideal.span (Set.range f) : Ideal A) : Set A) ⊆ {closedPoint A}
  | 0, J, hJ, _ => by
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    have hspan : Ideal.span (Set.range (Fin.elim0 : Fin 0 → A)) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hspan, sup_bot_eq]
    intro q hq
    by_contra hqm
    have hqJ : J ≤ q.asIdeal := (mem_zeroLocus _ _).mp hq
    have hmJ : closedPoint A ∈ zeroLocus (J : Set A) :=
      closedPoint_mem_zeroLocus fun h => q.2.ne_top (top_le_iff.mp (h ▸ hqJ))
    have hlt : (⟨q, hq⟩ : zeroLocus (J : Set A)) < ⟨closedPoint A, hmJ⟩ :=
      lt_of_le_of_ne (show q ≤ closedPoint A from le_top)
        (fun h => hqm (Set.mem_singleton_iff.mpr (congrArg Subtype.val h)))
    have h1 : (1 : WithBot ℕ∞) ≤ Order.krullDim (zeroLocus (J : Set A)) :=
      Order.one_le_krullDim_iff.mpr ⟨_, _, hlt⟩
    rw [← Order.krullDim_eq_of_orderIso J.primeSpectrumQuotientOrderIsoZeroLocus] at h1
    have := h1.trans hJ
    exact absurd this (by decide)
  | e + 1, J, hJ, hK => by
    by_cases hsub : zeroLocus (J : Set A) ⊆ {closedPoint A}
    · exact ⟨fun _ => 0, fun _ => K.zero_mem,
        (zeroLocus_anti_mono_ideal le_sup_left).trans hsub⟩
    · obtain ⟨q, hqJ, hqm⟩ := Set.not_subset.mp hsub
      have hK' : ∀ p ∈ J.minimalPrimes, ¬ K ≤ p := by
        intro p hp hKp
        refine hK ⟨p, hp.1.1⟩ hp.1.2 (fun hpm => ?_) hKp
        have hpm' : p = maximalIdeal A := congrArg PrimeSpectrum.asIdeal hpm
        have hqle : q.asIdeal ≤ p := hpm' ▸ le_maximalIdeal q.2.ne_top
        have hpq : p ≤ q.asIdeal := hp.2 ⟨q.2, (mem_zeroLocus _ _).mp hqJ⟩ hqle
        exact hqm (Set.mem_singleton_iff.mpr
          (PrimeSpectrum.ext ((le_antisymm hqle hpq).trans hpm')))
      obtain ⟨x, hxK, hx⟩ := exists_mem_ringKrullDim_quotient_sup_span_singleton_le K J e
        (by exact_mod_cast hJ) hK'
      obtain ⟨g, hgK, hg⟩ := exists_fin_mem_zeroLocus_sup_span_subset_closedPoint K e
        (J ⊔ Ideal.span {x}) hx (fun q hq => hK q (le_sup_left.trans hq))
      refine ⟨Fin.cons x g, fun i => Fin.cases hxK hgK i, ?_⟩
      have heq : J ⊔ Ideal.span (Set.range (Fin.cons x g : Fin (e + 1) → A)) =
          J ⊔ Ideal.span {x} ⊔ Ideal.span (Set.range g) := by
        rw [Fin.range_cons, Ideal.span_insert, sup_assoc]
      rwa [heq]

/-- **Stacks 0ECR, the main assertion.** Let `(A, 𝔪)` be a Noetherian complete local ring and
`I` a proper ideal; put `Y = V(I)`. For a closed `Z ⊆ Y` with
`dim(Z) < min(c, d - 1) - cd(A, I)`, the complement `Y ∖ Z` is connected. -/
theorem isConnected_zeroLocus_diff_of_krullDimToEInt_lt
    [IsAdicComplete (maximalIdeal A) A] (I : Ideal A) (hI : I ≠ ⊤)
    (Z : Set (PrimeSpectrum A)) (hZ : IsClosed Z) (hZY : Z ⊆ zeroLocus (I : Set A))
    (hdim : krullDimToEInt (topologicalKrullDim Z) <
      ((min (minDimDisconnectingClosed (PrimeSpectrum A) : ℤ)
          ((minDimIrreducibleComponent (PrimeSpectrum A) : ℤ) - 1) -
        cohomologicalDimension A I I.fg_of_isNoetherianRing : ℤ) : EInt)) :
    IsConnected (zeroLocus (I : Set A) \ Z) := by
  by_contra hnc
  set Y := zeroLocus (I : Set A) with hY
  set cd := cohomologicalDimension A I I.fg_of_isNoetherianRing with hcd
  set c := minDimDisconnectingClosed (PrimeSpectrum A)
  set d := minDimIrreducibleComponent (PrimeSpectrum A)
  rcases Set.eq_empty_or_nonempty Z with rfl | hZne
  · rw [Set.diff_empty] at hnc
    exact hnc (isConnected_zeroLocus I hI)
  have hmZ : closedPoint A ∈ Z := closedPoint_mem_of_isClosed hZ hZne
  set J := vanishingIdeal Z with hJdef
  have hZJ : zeroLocus (J : Set A) = Z := by
    rw [hJdef, zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
  obtain ⟨e, he, hZdim⟩ := exists_dim_eq_natCast_of_isClosed hZ hZne
  rw [hZdim, krullDimToEInt_natCast] at hdim
  have hdim' : (e : ℤ) < min (c : ℤ) ((d : ℤ) - 1) - cd := WithBotTop.coe_lt_coe.mp hdim
  -- the ideal `K` the `fᵢ` are taken in, and what it gives
  have key : ∃ K : Ideal A, K ≤ maximalIdeal A ∧
      (∀ q : PrimeSpectrum A, J ≤ q.asIdeal → q ≠ closedPoint A → ¬ K ≤ q.asIdeal) ∧
      ∀ F : Ideal A, F ≤ K → zeroLocus ((J ⊔ F : Ideal A) : Set A) ⊆ {closedPoint A} →
        ¬ IsConnected (zeroLocus ((I ⊔ F : Ideal A) : Set A) \ {closedPoint A}) := by
    -- the points of `V(I + F) ∖ {𝔪}` lie in `Y ∖ Z`
    have hsub : ∀ F : Ideal A, zeroLocus ((J ⊔ F : Ideal A) : Set A) ⊆ {closedPoint A} →
        zeroLocus ((I ⊔ F : Ideal A) : Set A) \ {closedPoint A} ⊆ Y \ Z := by
      intro F hF x ⟨hx, hxm⟩
      rw [zeroLocus_sup] at hx
      refine ⟨hx.1, fun hxZ => hxm (hF ?_)⟩
      rw [zeroLocus_sup, hZJ]
      exact ⟨hxZ, hx.2⟩
    rcases Set.eq_empty_or_nonempty (Y \ Z) with hempty | hYZne
    · refine ⟨maximalIdeal A, le_rfl, fun q _ hqm hmq => hqm
        (PrimeSpectrum.ext (le_antisymm (le_maximalIdeal q.2.ne_top) hmq)), ?_⟩
      intro F _ hF hconn
      obtain ⟨x, hx⟩ := hconn.nonempty
      have := hsub F hF hx
      rw [hempty] at this
      exact this
    · have hpre : ¬ IsPreconnected (Y \ Z) := fun h => hnc ⟨hYZne, h⟩
      simp only [IsPreconnected, not_forall, exists_prop] at hpre
      obtain ⟨u, v, hu, hv, huv, ⟨a, hau⟩, ⟨b, hbv⟩, huv'⟩ := hpre
      rw [Set.not_nonempty_iff_eq_empty] at huv'
      let U : Set (PrimeSpectrum A) := {closedPoint A}ᶜ
      -- a point of `(Y ∖ Z) ∩ w` closed in the punctured spectrum
      have hclosedPt : ∀ w : Set (PrimeSpectrum A), IsOpen w → ((Y \ Z) ∩ w).Nonempty →
          ∃ p : PrimeSpectrum A, p ∈ (Y \ Z) ∩ w ∧
            ∀ q : PrimeSpectrum A, p ≤ q → q ≠ closedPoint A → q = p := by
        intro w hw ⟨x, hx⟩
        have hlc : IsLocallyClosed (Subtype.val ⁻¹' ((Y \ Z) ∩ w) : Set U) := by
          refine IsLocallyClosed.preimage ?_ continuous_subtype_val
          rw [Set.diff_eq]
          exact ((isClosed_zeroLocus _).isLocallyClosed.inter
            hZ.isOpen_compl.isLocallyClosed).inter hw.isLocallyClosed
        have hxU : x ∈ U := fun hxm => hx.1.2 (Set.mem_singleton_iff.mp hxm ▸ hmZ)
        obtain ⟨⟨p, hpU⟩, hp, hpcl⟩ :=
          nonempty_inter_closedPoints (X := U) ⟨⟨x, hxU⟩, hx⟩ hlc
        refine ⟨p, hp, fun q hpq hqm => ?_⟩
        obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.mp (mem_closedPoints_iff.mp hpcl)
        have hpC : p ∈ C := by
          have : (⟨p, hpU⟩ : U) ∈ Subtype.val ⁻¹' C := hCeq ▸ rfl
          exact this
        have hqC : q ∈ C := ((le_iff_specializes p q).mp hpq).mem_closed hC hpC
        have : (⟨q, hqm⟩ : U) ∈ ({⟨p, hpU⟩} : Set U) := hCeq ▸ hqC
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp this)
      obtain ⟨w₁, hw₁, hw₁cl⟩ := hclosedPt u hu ⟨a, hau⟩
      obtain ⟨w₂, hw₂, hw₂cl⟩ := hclosedPt v hv ⟨b, hbv⟩
      refine ⟨w₁.asIdeal ⊓ w₂.asIdeal, inf_le_left.trans (le_maximalIdeal w₁.2.ne_top), ?_, ?_⟩
      · intro q hJq hqm hKq
        have hqZ : q ∈ Z := hZJ ▸ (mem_zeroLocus _ _).mpr hJq
        rcases (Ideal.IsPrime.inf_le q.2).mp hKq with h | h
        · exact hw₁.1.2 (hw₁cl q h hqm ▸ hqZ)
        · exact hw₂.1.2 (hw₂cl q h hqm ▸ hqZ)
      · intro F hFK hF hconn
        have hT := hsub F hF
        have hw : ∀ w : PrimeSpectrum A, w ∈ Y \ Z → F ≤ w.asIdeal →
            w ∈ zeroLocus ((I ⊔ F : Ideal A) : Set A) \ {closedPoint A} := by
          intro w hwYZ hFw
          refine ⟨?_, fun hwm => hwYZ.2 (Set.mem_singleton_iff.mp hwm ▸ hmZ)⟩
          rw [zeroLocus_sup]
          exact ⟨hwYZ.1, (mem_zeroLocus _ _).mpr hFw⟩
        have h₁ := hw w₁ hw₁.1 (hFK.trans inf_le_left)
        have h₂ := hw w₂ hw₂.1 (hFK.trans inf_le_right)
        obtain ⟨y, hyT, hyuv⟩ := hconn.isPreconnected u v hu hv
          ((hT).trans huv) ⟨w₁, h₁, hw₁.2⟩ ⟨w₂, h₂, hw₂.2⟩
        have : y ∈ (Y \ Z) ∩ (u ∩ v) := ⟨hT hyT, hyuv⟩
        rw [huv'] at this
        exact this
  obtain ⟨K, hKm, hK, hdisc⟩ := key
  obtain ⟨f, hfK, hf⟩ := exists_fin_mem_zeroLocus_sup_span_subset_closedPoint K e J he.le hK
  set F := Ideal.span (Set.range f)
  have hFK : F ≤ K := Ideal.span_le.mpr (Set.range_subset_iff.mpr hfK)
  have hI' : I ⊔ F ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ sup_le (le_maximalIdeal hI)
      (hFK.trans hKm)))
  have hnot := hdisc F hFK hf
  -- `cd(A, I + F) ≤ cd(A, I) + e`
  have hF : F.FG := F.fg_of_isNoetherianRing
  have hcdF : cohomologicalDimension A F hF ≤ (e : ℤ) :=
    cohomologicalDimension_le_card_generators A F hF f rfl
  have hcdsum := cohomologicalDimension_add_le A I F I.fg_of_isNoetherianRing hF
  have hcd1 : (-1 : ℤ) ≤ cd := (isLocalCohomologyBound_cohomologicalDimension A I _).1
  have hcd' : cohomologicalDimension A (I ⊔ F) (I ⊔ F).fg_of_isNoetherianRing ≤ cd + e := by
    have : cohomologicalDimension A (I ⊔ F) (I ⊔ F).fg_of_isNoetherianRing =
        cohomologicalDimension A (I + F) (Submodule.FG.sup I.fg_of_isNoetherianRing hF) := rfl
    rw [this]
    exact hcdsum.trans (max_le (by omega) (by omega))
  apply hnot
  refine isConnected_zeroLocus_diff_closedPoint_of_cohomologicalDimension_lt (I ⊔ F) hI' ?_ ?_
  · have := min_le_left (c : ℤ) ((d : ℤ) - 1)
    omega
  · have := min_le_right (c : ℤ) ((d : ℤ) - 1)
    omega

omit [IsNoetherianRing A] in
/-- The punctured spectrum of `A/I`, the non-maximal primes of `A/I`, is connected exactly when
`V(I) ∖ {𝔪}` is: the contraction along `A → A/I` is a closed embedding with image `V(I)`, under
which the closed point of `A/I` goes to `𝔪`. -/
theorem isConnected_setOf_not_isMaximal_quotient_iff (I : Ideal A) :
    IsConnected {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal} ↔
      IsConnected (zeroLocus (I : Set A) \ {closedPoint A}) := by
  let φ : PrimeSpectrum (A ⧸ I) → PrimeSpectrum A := comap (Ideal.Quotient.mk I)
  have hφ : IsInducing φ :=
    (isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isInducing
  have hfwd : ∀ p : PrimeSpectrum (A ⧸ I), p.asIdeal.IsMaximal → φ p = closedPoint A :=
    fun p _ => PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective))
  have hmax : ∀ p : PrimeSpectrum (A ⧸ I), p.asIdeal.IsMaximal ↔ φ p = closedPoint A := by
    refine fun p => ⟨hfwd p, fun hp => ?_⟩
    obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
    rw [comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (hp.trans (hfwd ⟨M, hM.isPrime⟩ hM).symm)]
    exact hM
  have himage : φ '' {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal} =
      zeroLocus (I : Set A) \ {closedPoint A} := by
    have hrange : Set.range φ = zeroLocus (I : Set A) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hrange ▸ Set.mem_range_self p, fun h => hp ((hmax p).mpr h)⟩
    · rintro ⟨hx, hxm⟩
      obtain ⟨p, rfl⟩ := hrange ▸ hx
      exact ⟨p, fun h => hxm ((hmax p).mp h), rfl⟩
  rw [← himage, IsConnected, IsConnected, Set.image_nonempty, hφ.isPreconnected_image]

/-- **Stacks Project, Tag 0ECR** (Varbaro, Theorem 1.6). Let `(A, 𝔪)` be a Noetherian complete
local ring and `I` a proper ideal of `A`. Set `X = Spec(A)` and `Y = V(I)`, and denote by

1. `d` the minimal dimension of an irreducible component of `X`
   (`minDimIrreducibleComponent`), and
2. `c` the minimal dimension of a closed subset `Z ⊆ X` such that `X ∖ Z` is disconnected
   (`minDimDisconnectingClosed`).

Then for `Z ⊆ Y` closed, `Y ∖ Z` is connected if `dim(Z) < min(c, d - 1) - cd(A, I)`. In
particular, the punctured spectrum of `A/I` is connected if `cd(A, I) < min(c, d - 1)`.

Both minima are attained (`exists_irreducibleComponent_topologicalKrullDim_eq_minDim`,
`exists_isClosed_not_isConnected_compl_topologicalKrullDim_eq_minDim`). The dimension of `Z` is
its Krull dimension, `⊥` for `Z = ∅`, compared with the integer `min(c, d - 1) - cd(A, I)` in the
extended integers. The punctured spectrum of `A/I` is the set of its non-maximal primes. -/
@[stacks 0ECR "both assertions: the connectedness of Y ∖ Z for closed Z ⊆ Y with \
dim(Z) < min(c, d - 1) - cd(A, I), and of the punctured spectrum of A/I when \
cd(A, I) < min(c, d - 1)", sga "2 XIII 2.1" "more general"]
theorem isConnected_zeroLocus_diff_and_isConnected_puncturedSpectrum_quotient
    [IsAdicComplete (maximalIdeal A) A] (I : Ideal A) (hI : I ≠ ⊤) :
    (∀ Z : Set (PrimeSpectrum A), IsClosed Z → Z ⊆ zeroLocus (I : Set A) →
      krullDimToEInt (topologicalKrullDim Z) <
        ((min (minDimDisconnectingClosed (PrimeSpectrum A) : ℤ)
            ((minDimIrreducibleComponent (PrimeSpectrum A) : ℤ) - 1) -
          cohomologicalDimension A I I.fg_of_isNoetherianRing : ℤ) : EInt) →
      IsConnected (zeroLocus (I : Set A) \ Z)) ∧
    (cohomologicalDimension A I I.fg_of_isNoetherianRing <
        min (minDimDisconnectingClosed (PrimeSpectrum A) : ℤ)
          ((minDimIrreducibleComponent (PrimeSpectrum A) : ℤ) - 1) →
      IsConnected {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal}) :=
  ⟨isConnected_zeroLocus_diff_of_krullDimToEInt_lt I hI, fun h =>
    (isConnected_setOf_not_isMaximal_quotient_iff I).mpr
      (isConnected_zeroLocus_diff_closedPoint_of_cohomologicalDimension_lt I hI
        (h.trans_le (min_le_left _ _)) (h.trans_le (min_le_right _ _)))⟩

end Local

end Stacks.Algebraization

end
