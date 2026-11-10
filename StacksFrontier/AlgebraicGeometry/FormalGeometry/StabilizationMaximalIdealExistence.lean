module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationReduction

/-!
# The conclusion of Stacks 0DXM

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be a finite `A`-module
and fix integers `s` and `d`. Stacks 0DXM asserts, under hypotheses (1)–(4) recorded in
`Stacks.Algebraization.LocalStabilizationHypotheses`, that there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` such that every further ideal `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` has
`RΓ_{J₀}(M) → RΓ_J(M)` an isomorphism in cohomology in degrees `≤ s`, and such that a single
power of `J₀ I` annihilates all of those cohomology modules.

`Stacks.Algebraization.exists_stabilization_of_exists` states exactly that conclusion, but with
the existence statement of Stacks 0EFI at `J = 𝔪` carried as a hypothesis. This file discharges
that hypothesis and so proves the conclusion outright.

For `0 ≤ d` the existence statement is `Stacks.Algebraization.exists_isStabilizingData`. The
remaining case `d < 0` is not covered by it — the source of that lemma uses `0 ≤ d` silently when
it reads `depth + dim > d + s` as `depth + dim > s` — and is settled here by a different route.
A negative `d` makes hypothesis (3) of Stacks 0DXM *stronger*, not weaker: the dimension of
`A/𝔭` is never negative, so (3) says that no prime outside `V(I)` has `V(𝔭) ∩ V(I) = {𝔪}`. In a
Noetherian local ring that forces `V(I) = Spec(A)`: a prime maximal among those avoiding a fixed
`f ∈ I` has exactly one prime strictly above it, namely `𝔪`, so its own closed set meets `V(I)`
in `{𝔪}` and (3) excludes it. Hence `I` is nilpotent, and the conclusion is immediate — the
admissible ideals `J ⊆ J₀` all have `V(J) = V(𝔪)`, so the comparison is an isomorphism in every
degree, and a power of `I` alone is zero.

## Main results

* `Stacks.Algebraization.forall_le_of_forall_zeroLocus_inter_ne_closedPoint` — in a Noetherian
  local ring, if no prime outside `V(I)` has `V(𝔭) ∩ V(I) = {𝔪}`, then every prime contains `I`.
* `Stacks.Algebraization.exists_isStabilizingData_maximalIdeal` — the existence statement of
  Stacks 0EFI at `J = 𝔪`, with no hypothesis beyond (1)–(4) of Stacks 0DXM.
* `Stacks.Algebraization.exists_stabilization` — **Stacks 0DXM**, the whole conclusion.

## Implementation notes

The direction of the comparison is `RΓ_{J₀}(M) → RΓ_J(M)` for `J ≤ J₀`, as in
`Stacks.Algebraization.localCohomologyComparison`; see the module documentation of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal` for why the source's
direction is the one with no canonical map.

The module is in the universe of the ring, because
`Stacks.Algebraization.exists_isStabilizingData` is, Faltings' annihilator theorem Stacks 0EFC
being stated there for a module over a ring of the same universe. The `d < 0` branch below is
universe-polymorphic in the module; only the `0 ≤ d` branch is not.

The step from (3) to the nilpotence of `I` uses Krull's principal ideal theorem in the relative
form `Ideal.map_height_le_one_of_mem_minimalPrimes`, prime avoidance, and the finiteness of the
set of minimal primes over an ideal of a Noetherian ring. It needs no catenary hypothesis: a
prime `𝔭` maximal among those avoiding `f` has the property that every prime strictly above it
contains `f`, and the argument shows that such a `𝔭` cannot carry a chain `𝔭 < 𝔮 < 𝔪`, because
the minimal primes over `𝔭 + (f)` would then be finitely many primes of relative height one
covering `𝔪`.

## References

* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)

## Tags

local cohomology, depth, annihilator, algebraization, local ring
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Primes with exactly the maximal ideal above them -/

section Spectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The image of a strict inclusion of ideals above `p` under `A → A/p` is strict. -/
private theorem map_quotient_lt_map_quotient {p q r : Ideal A} (hpq : p ≤ q) (hqr : q < r) :
    q.map (Ideal.Quotient.mk p) < r.map (Ideal.Quotient.mk p) := by
  refine lt_of_le_of_ne (Ideal.map_mono hqr.le) fun hEq ↦ hqr.ne ?_
  have h := congrArg (Ideal.comap (Ideal.Quotient.mk p)) hEq
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    show Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (A ⧸ p)) = p from Ideal.mk_ker] at h
  have h1 : q ⊔ p = q := sup_eq_left.mpr hpq
  have h2 : r ⊔ p = r := sup_eq_left.mpr (hpq.trans hqr.le)
  rw [← h1, h, h2]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A prime strictly above `p` has positive height in `A/p`. -/
private theorem one_le_height_map_quotient {p q : Ideal A} [p.IsPrime] (h : p < q) :
    1 ≤ (q.map (Ideal.Quotient.mk p)).height := by
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]
  exact fun hle ↦ h.not_ge hle

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The image of a prime above `p` is prime in `A/p`. -/
private theorem isPrime_map_quotient {p q : Ideal A} (hq : q.IsPrime) (hpq : p ≤ q) :
    (q.map (Ideal.Quotient.mk p)).IsPrime :=
  have := hq
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- A prime maximal among those avoiding `f` has only the maximal ideal strictly above it.

If a chain `p < q < 𝔪` existed, then `𝔪` would have height at least two in `A/p`, so `𝔪` would
not be minimal over `p + (f)`, whose minimal primes have height at most one in `A/p` by Krull's
principal ideal theorem. Those minimal primes are finitely many primes, so by prime avoidance
some `g ∈ 𝔪` avoids them all; a prime minimal over `p + (g)` then has height at most one in
`A/p` and contains `f` by maximality of `p`, hence equals one of them — but it contains `g`. -/
private theorem eq_maximalIdeal_of_maximal_notMem {f : A} (hf : f ∈ maximalIdeal A) {p : Ideal A}
    [hp : p.IsPrime] (hfp : f ∉ p) (hmax : ∀ q : Ideal A, q.IsPrime → p < q → f ∈ q)
    {q : Ideal A} (hq : q.IsPrime) (hpq : p < q) : q = maximalIdeal A := by
  classical
  by_contra hne
  have hqm : q < maximalIdeal A := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hq.ne_top) hne
  have hle : ∀ g : A, g ∈ maximalIdeal A → p ⊔ Ideal.span {g} ≤ maximalIdeal A := fun g hg ↦
    sup_le (IsLocalRing.le_maximalIdeal hp.ne_top) (Ideal.span_le.mpr (by simpa using hg))
  have hne_top : ∀ g : A, g ∈ maximalIdeal A → p ⊔ Ideal.span {g} ≠ ⊤ := fun g hg h ↦
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hle g hg))
  -- The minimal primes over `p + (f)`: finitely many, each of relative height one.
  have hBfin : (p ⊔ Ideal.span {f}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A (p ⊔ Ideal.span {f})
  have hBle : ∀ b ∈ (p ⊔ Ideal.span {f}).minimalPrimes, p ≤ b ∧ f ∈ b := fun b hb ↦
    ⟨le_sup_left.trans hb.1.2, hb.1.2 (le_sup_right (b := Ideal.span {f})
      (Ideal.mem_span_singleton_self f))⟩
  -- `𝔪` is not one of them: it has height at least two in `A/p`.
  have hmB : maximalIdeal A ∉ (p ⊔ Ideal.span {f}).minimalPrimes := by
    intro hmem
    have := isPrime_map_quotient hq hpq.le
    have := isPrime_map_quotient (IsLocalRing.maximalIdeal.isMaximal A).isPrime
      (hpq.le.trans hqm.le)
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes (x := f) (I := p) hmem
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (map_quotient_lt_map_quotient hpq.le hqm)
    have h3 : (1 : ℕ∞) + 1 ≤ 1 :=
      le_trans (le_trans (add_le_add (one_le_height_map_quotient hpq) le_rfl) h2) h1
    exact absurd ((ENat.add_one_le_iff (by simp)).mp h3) (lt_irrefl 1)
  -- Prime avoidance: some `g ∈ 𝔪` avoids all of them.
  have hsub : ¬ ((maximalIdeal A : Set A) ⊆
      ⋃ b ∈ (p ⊔ Ideal.span {f}).minimalPrimes, (b : Set A)) := fun h ↦ hmB
    ((Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hBfin ⊥ ⊥
      (fun b hb _ _ ↦ hb.isPrime) bot_ne_top bot_ne_top).mp h)
  rw [Set.not_subset] at hsub
  obtain ⟨g, hgm, hgB⟩ := hsub
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hgB
  obtain ⟨b₀, hb₀⟩ := Ideal.nonempty_minimalPrimes (hne_top f hf)
  have hgp : g ∉ p := fun h ↦ hgB b₀ hb₀ ((hBle b₀ hb₀).1 h)
  -- A prime minimal over `p + (g)`.
  obtain ⟨c, hc⟩ := Ideal.nonempty_minimalPrimes (hne_top g hgm)
  have hcp : c.IsPrime := hc.1.1
  have hgc : g ∈ c := hc.1.2 (le_sup_right (b := Ideal.span {g}) (Ideal.mem_span_singleton_self g))
  have hpc : p < c := lt_of_le_of_ne (le_sup_left.trans hc.1.2) fun h ↦ hgp (h ▸ hgc)
  have hfc : f ∈ c := hmax c hcp hpc
  obtain ⟨b, hb, hbc⟩ : ∃ b ∈ (p ⊔ Ideal.span {f}).minimalPrimes, b ≤ c :=
    Ideal.exists_minimalPrimes_le (sup_le hpc.le (Ideal.span_le.mpr (by simpa using hfc)))
  rcases eq_or_lt_of_le hbc with rfl | hlt
  · exact hgB b hb hgc
  · have := isPrime_map_quotient hb.1.1 (hBle b hb).1
    have := isPrime_map_quotient hcp hpc.le
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes (x := g) (I := p) hc
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
      (map_quotient_lt_map_quotient (hBle b hb).1 hlt)
    have h3 : (1 : ℕ∞) + 1 ≤ 1 :=
      le_trans (le_trans (add_le_add
        (one_le_height_map_quotient (lt_of_le_of_ne (hBle b hb).1
          fun h ↦ hfp (h ▸ (hBle b hb).2))) le_rfl) h2) h1
    exact absurd ((ENat.add_one_le_iff (by simp)).mp h3) (lt_irrefl 1)

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A prime maximal among those avoiding `f`, above a given prime avoiding `f`. -/
private theorem exists_maximal_prime_notMem {f : A} {p₀ : Ideal A} [hp₀ : p₀.IsPrime]
    (hf : f ∉ p₀) :
    ∃ p : Ideal A, p.IsPrime ∧ f ∉ p ∧ ∀ q : Ideal A, q.IsPrime → p < q → f ∈ q := by
  have hdisj : Disjoint (p₀ : Set A) (Submonoid.powers f) := by
    rw [Set.disjoint_right]
    rintro x ⟨n, rfl⟩ hx
    exact hf (hp₀.mem_of_pow_mem n hx)
  have ih : ∀ c ⊆ {p : Ideal A | Disjoint (p : Set A) (Submonoid.powers f)},
      IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {p : Ideal A | Disjoint (p : Set A) (Submonoid.powers f)}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hc' x hx
    cases isEmpty_or_nonempty c
    · exact ⟨x, hc hx, fun J hJ ↦ isEmptyElim (⟨J, hJ⟩ : c)⟩
    refine ⟨sSup c, Set.disjoint_left.mpr fun y hy ↦ ?_, fun _ ↦ le_sSup⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hy)
    exact Set.disjoint_left.mp (hc r.2) hr
  obtain ⟨p, -, hp⟩ := zorn_le_nonempty₀ _ ih p₀ hdisj
  refine ⟨p, Ideal.isPrime_of_maximally_disjoint _ _ hp.1 (fun _ ↦ hp.not_prop_of_gt),
    Set.disjoint_right.mp hp.1 (Submonoid.mem_powers f), fun q hq hlt ↦ ?_⟩
  obtain ⟨x, hxq, n, rfl⟩ := Set.not_disjoint_iff.mp (hp.not_prop_of_gt hlt)
  exact hq.mem_of_pow_mem n hxq

/-- If no prime outside `V(I)` has `V(𝔭) ∩ V(I) = {𝔪}`, then every prime of a Noetherian local
ring contains `I`.

This is the content of hypothesis (3) of Stacks 0DXM when `d < 0`: the dimension of `A/𝔭` is
never negative, so the hypothesis cannot be met by any prime outside `V(I)` and must instead say
that there is none with `V(𝔭) ∩ V(I) = {𝔪}`. -/
public theorem forall_le_of_forall_zeroLocus_inter_ne_closedPoint {I : Ideal A} (hI : I ≠ ⊤)
    (h : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ≠
        {closedPoint A})
    (p : Ideal A) (hp : p.IsPrime) : I ≤ p := by
  by_contra hcon
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hcon
  have := hp
  obtain ⟨r, hr, hfr, hmax⟩ := exists_maximal_prime_notMem (p₀ := p) hfp
  have := hr
  have hfm : f ∈ maximalIdeal A := IsLocalRing.le_maximalIdeal hI hfI
  refine h ⟨r, hr⟩ (fun hmem ↦ hfr (hmem hfI)) (Set.Subset.antisymm (fun x hx ↦ ?_)
    (Set.singleton_subset_iff.2
      ⟨closedPoint_mem_zeroLocus hr.ne_top, closedPoint_mem_zeroLocus hI⟩))
  have hrx : r ≤ x.asIdeal := hx.1
  have hIx : I ≤ x.asIdeal := hx.2
  refine Set.mem_singleton_iff.2 (PrimeSpectrum.ext ?_)
  rcases eq_or_lt_of_le hrx with heq | hlt
  · exact absurd (heq ▸ hIx hfI) hfr
  · exact eq_maximalIdeal_of_maximal_notMem hfm hfr hmax x.2 hlt

end Spectrum

/-! ### The existence statement at the maximal ideal -/

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A nilpotent ideal `I` makes the conclusion of Stacks 0EFI at `J = 𝔪` immediate: every
admissible shrinking `J ≤ 𝔪` has `V(J) = V(𝔪)`, so the comparison is an isomorphism in every
degree, and some power of `I` alone is zero. -/
private theorem exists_isStabilizingData_maximalIdeal_of_forall_le {I : Ideal A} (s : ℤ)
    (h : ∀ p : Ideal A, p.IsPrime → I ≤ p) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I (maximalIdeal A) s p := by
  have hrad : I ≤ (⊥ : Ideal A).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun J hJ ↦ h J hJ.2
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad I.fg_of_isNoetherianRing
  have huniv : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ :=
    Set.eq_univ_of_forall fun p ↦ h p.asIdeal p.2
  refine ⟨(maximalIdeal A, n), le_rfl, rfl, ?_, ?_⟩
  · intro J hJ hVJ i _
    have hV : PrimeSpectrum.zeroLocus (J : Set A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) := by
      simpa [huniv] using hVJ
    have := isIso_localCohomologyComparison_of_zeroLocus_eq (maximalIdeal A) J
      (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing hJ hV
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
    infer_instance
  · intro J _ _ i _
    exact le_trans (le_trans (pow_le_pow_left' Ideal.mul_le_right n) hn) bot_le

/-- **The existence statement of Stacks 0EFI at `J = 𝔪`.** Under hypotheses (1)–(4) of Stacks
0DXM there is a pair `(J₀, n)` with the stabilization property of Stacks 0EFI for `J = 𝔪`.

For `0 ≤ d` this is `Stacks.Algebraization.exists_isStabilizingData`. For `d < 0` hypothesis (3)
of Stacks 0DXM says that no prime outside `V(I)` has `V(𝔭) ∩ V(I) = {𝔪}`, since the dimension of
`A/𝔭` is never negative; by
`Stacks.Algebraization.forall_le_of_forall_zeroLocus_inter_ne_closedPoint` the ideal `I` is then
contained in every prime, hence nilpotent, and the conclusion is immediate. -/
public theorem exists_isStabilizingData_maximalIdeal (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : LocalStabilizationHypotheses (M := M) I s d omega) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I (maximalIdeal A) s p := by
  rcases le_or_gt 0 d with hd | hd
  · exact exists_isStabilizingData I (maximalIdeal A) s d hd omega H.toStabilizationHypotheses
  · refine exists_isStabilizingData_maximalIdeal_of_forall_le s
      (forall_le_of_forall_zeroLocus_inter_ne_closedPoint H.ne_top (fun p hp hV ↦ ?_))
    have hbound := H.dimensionBound p hp hV
    have hnn : (0 : EInt) ≤ krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) := by
      have hpos : (0 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) :=
        have : Nontrivial (A ⧸ p.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr p.2.ne_top
        ringKrullDim_nonneg_of_nontrivial
      revert hpos
      induction ringKrullDim (A ⧸ p.asIdeal) using WithBot.recBotCoe with
      | bot => intro hpos; simp at hpos
      | coe m =>
        intro _
        cases m using ENat.recTopCoe with
        | top => exact le_top
        | coe k =>
          refine le_trans ?_ (le_of_eq (krullDimToEInt_natCast k).symm)
          exact_mod_cast WithBotTop.coe_le_coe.mpr (by exact_mod_cast Int.natCast_nonneg k)
    have hneg : (d : EInt) < 0 := by
      refine lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by exact_mod_cast hd)) (le_of_eq ?_)
      rfl
    exact absurd (hnn.trans hbound) (not_le_of_gt hneg)

/-! ### The conclusion of Stacks 0DXM -/

/-- **Stacks 0DXM.** Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be
a finite `A`-module and let `s` and `d` be integers. Under hypotheses (1)–(4) of the lemma there
is an ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that for every ideal `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}` the comparison `RΓ_{J₀}(M) → RΓ_J(M)` induces an isomorphism in cohomology
in degrees `≤ s`, and one power of `J₀ I` annihilates all of those cohomology modules.

This is `Stacks.Algebraization.exists_stabilization_of_exists` with its hypothesis discharged by
`Stacks.Algebraization.exists_isStabilizingData_maximalIdeal`. Taking `J = J₀` gives the
annihilation of `H^i_{J₀}(M)` by a power of `J₀ I`. -/
@[stacks 0DXM "the conclusion: an ideal J₀ and one exponent n such that every J ⊆ J₀ with \
V(J) ∩ V(I) = {𝔪} has RΓ_{J₀}(M) → RΓ_J(M) an isomorphism on cohomology in degrees ≤ s and \
(J₀ I) ^ n annihilating those modules"]
public theorem exists_stabilization (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : LocalStabilizationHypotheses (M := M) I s d omega) :
    ∃ J₀ : Ideal A, ∃ n : ℕ,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, ∀ hJ : J ≤ J₀,
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℤ, i ≤ s →
            IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                (localCohomologyComparison A J₀ J J₀.fg_of_isNoetherianRing
                  J.fg_of_isNoetherianRing hJ
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A M)))) ∧
              (J₀ * I) ^ n ≤ Module.annihilator A
                ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
                  ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
                    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                      (ModuleCat.of A M))).obj) :=
  exists_stabilization_of_exists I s d omega H
    (exists_isStabilizingData_maximalIdeal I s d omega H)

end

end Stacks.Algebraization

end
