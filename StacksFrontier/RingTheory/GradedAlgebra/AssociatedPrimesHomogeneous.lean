module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.FinitelyGenerated

/-!
# Associated primes of a homogeneous ideal are homogeneous

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a nonnegatively graded commutative ring and let `I` be a homogeneous
ideal of `A`. This file proves that every prime of the form `(I : x) = {r | r * x ∈ I}` is again
homogeneous, and deduces that every associated prime of `I` is homogeneous.

## Main results

* `Stacks.GradedRing.colon_singleton_eq_of_sub_mem`: the colon ideal `(I : x)` depends only on
  `x` modulo `I`.
* `Stacks.GradedRing.proj_mul_left_eq`: the degree-`(j + m)` component of `y * x`, for `y`
  homogeneous of degree `j`, is `y` times the degree-`m` component of `x`.
* `Stacks.GradedRing.mul_mem_isHomogeneous_iff_forall_proj`: for `y` homogeneous, `y * x` lies in
  a homogeneous ideal exactly when `y` times each homogeneous component of `x` does.
* `Stacks.GradedRing.exists_top_degree`: a nonzero element has a top degree.
* `Stacks.GradedRing.exists_trimmed_colon_singleton_eq`: an element may be replaced, without
  changing its colon ideal, by one whose components in `I` have been deleted.
* `Stacks.GradedRing.isHomogeneous_of_isPrime_colon_singleton`: **a prime colon ideal of a
  homogeneous ideal is homogeneous.**
* `Stacks.GradedRing.isHomogeneous_of_mem_associatedPrimes`: **over a Noetherian graded ring,
  every associated prime of a homogeneous ideal is homogeneous.**
* `Stacks.GradedRing.exists_mem_degree_notMem_of_saturated` and
  `Stacks.GradedRing.not_irrelevant_le_of_saturated`: **a prime colon ideal of a saturated ideal
  misses some element of every homogeneous component, so it does not contain the irrelevant
  ideal.**
* `Stacks.GradedRing.isHomogeneous_and_not_irrelevant_le_of_mem_associatedPrimes`: **the associated
  primes of a saturated homogeneous ideal are homogeneous and relevant.**

## Implementation notes

The proof needs no Noetherian hypothesis and no finiteness; only the corollary does, and there
only to remove the radical from Mathlib's definition of `Submodule.IsAssociatedPrime`, via
`Submodule.isAssociatedPrime_iff`.

Write `x_n` for the degree-`n` component of `x` and `p = (I : x)`. The argument is:

* the colon ideal is unchanged when `x` is altered by an element of `I`
  (`colon_singleton_eq_of_sub_mem`), so `x` may be *trimmed*: every component of `x` lying in `I`
  may be deleted (`exists_trimmed_colon_singleton_eq`, which needs no homogeneity of `I`, the
  deleted components being individually in `I`). A trimmed `x` has the property that each of its
  *nonzero* components lies outside `I`;
* among all trimmed `x` with `(I : x) = p`, choose one whose decomposition has the fewest nonzero
  components. If `b` is homogeneous and `b ∉ p` then `(I : b * x) = p` as well, because `p` is
  prime; so if `b` killed one component of `x` modulo `I`, trimming `b * x` would produce a
  competitor with strictly fewer components. Hence for homogeneous `b ∉ p` and every nonzero
  component `x_m`, the product `b * x_m` lies outside `I`;
* let `n₀` be the top degree of `x` and let `r ∈ p` have top degree `g`. The degree-`(g + n₀)`
  component of `r * x` is `r_g * x_{n₀}` (`proj_mul_top`), and it lies in `I` because `I` is
  homogeneous. By the previous step `r_g ∈ p`, so `r - r_g ∈ p` has strictly smaller support, and
  induction on the size of the support puts every component of `r` in `p`.

The top-degree product formula is proved here as a private lemma over `ℕ`. Its general form for an
ordered index monoid already exists as `Stacks.GradedRing.proj_mul_of_unique_pair`, but that
declaration lives in `StacksFrontier/AlgebraicGeometry/ProjIdealSheaf/HomogeneousGenerator.lean`,
whose import closure is the whole `Proj` development; a `StacksFrontier/RingTheory/` module must not
depend on that. Promoting the general lemma into this directory is the right repo-tier fix; it is
reported rather than done here, because it would move a declaration out of a reviewed file.

Extremal degrees are produced as existence statements rather than as `Finset.max'` of the support,
so that the decidability instance `∀ i (y : 𝒜 i), Decidable (y ≠ 0)` stays inside the proofs where
`classical` supplies it — the convention
`StacksFrontier/AlgebraicGeometry/ProjIdealSheaf/HomogeneousGenerator.lean` already uses.

Saturation is written out as the hypothesis
`∀ x, (∃ N, ∀ y ∈ 𝒜 N, y * x ∈ I) → x ∈ I` rather than introduced as a predicate. The notion
already has several ad-hoc spellings in this repository — the set
`{x | ∃ n, ∀ y ∈ 𝒜 n, y * x ∈ I}` in
`StacksFrontier/AlgebraicGeometry/ProjSaturation/Quotient.lean` and the `𝒜₊`-power-torsion form
in `StacksFrontier/AlgebraicGeometry/ProjSaturation/Basic.lean` — and coining a name here would
make a fourth.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public section

open DirectSum SetLike GradedRing

namespace Stacks.GradedRing

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]

/-- Membership in the colon ideal of a singleton, written with multiplication. -/
private theorem mem_colon_singleton_mul {I : Ideal A} {x r : A} :
    r ∈ I.colon {x} ↔ r * x ∈ I := by
  rw [Submodule.mem_colon_singleton, smul_eq_mul]

/-- The colon ideal of a singleton depends only on the element modulo the ideal. -/
theorem colon_singleton_eq_of_sub_mem {I : Ideal A} {x y : A} (h : x - y ∈ I) :
    I.colon {x} = I.colon {y} := by
  have key : ∀ u v : A, u - v ∈ I → ∀ r : A, r * u ∈ I → r * v ∈ I := by
    intro u v huv r hr
    rw [show r * v = r * u - r * (u - v) from by ring]
    exact sub_mem hr (I.mul_mem_left _ huv)
  refine le_antisymm (fun r hr => ?_) (fun r hr => ?_) <;>
    simp only [mem_colon_singleton_mul] at hr ⊢
  · exact key x y h r hr
  · exact key y x (by simpa using neg_mem h) r hr

variable (𝒜 : ℕ → σ) [_root_.GradedRing 𝒜]

/-- **The homogeneous components of `y * x` for `y` homogeneous of degree `j`.** The degree-`j + m`
component of `y * x` is `y` times the degree-`m` component of `x`. -/
theorem proj_mul_left_eq {y : A} {j : ℕ} (hy : y ∈ 𝒜 j) (x : A) (m : ℕ) :
    proj 𝒜 (j + m) (y * x) = y * proj 𝒜 m x := by
  rw [mul_comm y x, _root_.proj_mul_eq 𝒜 x y j (j + m) hy (Nat.le_add_right j m),
    show j + m - j = m from by omega, mul_comm]

/-- **A product with a homogeneous element lies in a homogeneous ideal exactly when all the
degreewise products do.** -/
theorem mul_mem_isHomogeneous_iff_forall_proj {I : Ideal A} (hI : Ideal.IsHomogeneous 𝒜 I)
    {y : A} {j : ℕ} (hy : y ∈ 𝒜 j) (x : A) :
    y * x ∈ I ↔ ∀ m : ℕ, y * proj 𝒜 m x ∈ I := by
  classical
  refine ⟨fun h m => ?_, fun h => ?_⟩
  · have hmem := hI (j + m) h
    rw [← GradedRing.proj_apply, proj_mul_left_eq 𝒜 hy x m] at hmem
    exact hmem
  · have hmul : y * x = ∑ m ∈ (decompose 𝒜 x).support, y * (decompose 𝒜 x m : A) := by
      rw [← Finset.mul_sum, DirectSum.sum_support_decompose 𝒜 x]
    rw [hmul]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [← GradedRing.proj_apply]
    exact h m

/-- A nonzero element of a nonnegatively graded ring has a top degree. -/
theorem exists_top_degree {x : A} (hx : x ≠ 0) :
    ∃ q : ℕ, proj 𝒜 q x ≠ 0 ∧ ∀ i : ℕ, q < i → proj 𝒜 i x = 0 := by
  classical
  have hsne : (decompose 𝒜 x).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hx (by rw [← DirectSum.sum_support_decompose 𝒜 x, he, Finset.sum_empty])
  refine ⟨(decompose 𝒜 x).support.max' hsne,
    (GradedRing.mem_support_iff 𝒜 x _).mp (Finset.max'_mem _ hsne), fun i hi => ?_⟩
  by_contra hc
  exact absurd (Finset.le_max' _ i ((GradedRing.mem_support_iff 𝒜 x i).mpr hc)) (not_le.mpr hi)

/-- **Trimming an element against a homogeneous ideal.** Every element `x` can be replaced, without
changing the colon ideal `(I : x)`, by an element whose homogeneous components agree with those of
`x` in the degrees where they avoid `I`, and vanish in the degrees where they do not. -/
theorem exists_trimmed_colon_singleton_eq (I : Ideal A) (x : A) :
    ∃ y : A, I.colon {y} = I.colon {x} ∧ (∀ m : ℕ, proj 𝒜 m x ∈ I → proj 𝒜 m y = 0) ∧
      ∀ m : ℕ, proj 𝒜 m x ∉ I → proj 𝒜 m y = proj 𝒜 m x := by
  classical
  set s : Finset ℕ := (decompose 𝒜 x).support with hs
  set u : Finset ℕ := s.filter fun m => ¬proj 𝒜 m x ∈ I with hu
  have hmemu : ∀ d ∈ u, proj 𝒜 d (∑ m ∈ u, proj 𝒜 m x) = proj 𝒜 d x := by
    intro d hd
    rw [map_sum, Finset.sum_eq_single_of_mem d hd fun b _ hb =>
        _root_.proj_eq_zero_of_mem_ne 𝒜 (_root_.proj_mem 𝒜 x b) hb,
      _root_.proj_eq_self_of_mem 𝒜 (_root_.proj_mem 𝒜 x d)]
  have hnotu : ∀ d : ℕ, d ∉ u → proj 𝒜 d (∑ m ∈ u, proj 𝒜 m x) = 0 := by
    intro d hd
    rw [map_sum]
    exact Finset.sum_eq_zero fun b hb =>
      _root_.proj_eq_zero_of_mem_ne 𝒜 (_root_.proj_mem 𝒜 x b) fun hbd => hd (hbd ▸ hb)
  refine ⟨∑ m ∈ u, proj 𝒜 m x, ?_, ?_, ?_⟩
  · refine colon_singleton_eq_of_sub_mem ?_
    have hx : ∑ m ∈ s, proj 𝒜 m x = x := by
      simp only [GradedRing.proj_apply, hs]
      exact DirectSum.sum_support_decompose 𝒜 x
    have hsplit : (∑ m ∈ s.filter fun m => proj 𝒜 m x ∈ I, proj 𝒜 m x) +
        (∑ m ∈ u, proj 𝒜 m x) = x := by
      rw [hu, Finset.sum_filter_add_sum_filter_not s (fun m => proj 𝒜 m x ∈ I)
        fun m => proj 𝒜 m x]
      exact hx
    rw [show (∑ m ∈ u, proj 𝒜 m x) - x =
        -∑ m ∈ s.filter fun m => proj 𝒜 m x ∈ I, proj 𝒜 m x from by
      linear_combination hsplit]
    exact neg_mem (Ideal.sum_mem _ fun m hm => (Finset.mem_filter.mp hm).2)
  · intro m hm
    exact hnotu m fun hc => (Finset.mem_filter.mp hc).2 hm
  · intro m hm
    refine hmemu m (Finset.mem_filter.mpr ⟨?_, hm⟩)
    rw [hs, GradedRing.mem_support_iff]
    exact fun h0 => hm (h0 ▸ I.zero_mem)

/-- A trimmed replacement `y` of `x` has no nonzero component in `I`. -/
private theorem proj_eq_zero_of_mem_of_trimmed {I : Ideal A} {x y : A}
    (h1 : ∀ m : ℕ, proj 𝒜 m x ∈ I → proj 𝒜 m y = 0)
    (h2 : ∀ m : ℕ, proj 𝒜 m x ∉ I → proj 𝒜 m y = proj 𝒜 m x) (m : ℕ) (hm : proj 𝒜 m y ∈ I) :
    proj 𝒜 m y = 0 := by
  by_cases hmx : proj 𝒜 m x ∈ I
  · exact h1 m hmx
  · exact absurd ((h2 m hmx) ▸ hm) hmx

/-- The top-degree component of a product, over `ℕ`. If `r` has no component above degree `g` and
`x` none above degree `n₀`, then the degree-`(g + n₀)` component of `r * x` is the product of the
two top components.

The general form over an ordered index monoid is `Stacks.GradedRing.proj_mul_of_unique_pair`,
which cannot be imported here; see the module docstring. -/
private theorem proj_mul_top {r x : A} {g n₀ : ℕ} (hgtop : ∀ i : ℕ, g < i → proj 𝒜 i r = 0)
    (hn₀top : ∀ i : ℕ, n₀ < i → proj 𝒜 i x = 0) :
    proj 𝒜 (g + n₀) (r * x) = proj 𝒜 g r * proj 𝒜 n₀ x := by
  classical
  have hle : ∀ n ∈ (decompose 𝒜 x).support, n ≤ n₀ := by
    intro n hn
    by_contra hc
    exact (GradedRing.mem_support_iff 𝒜 x n).mp hn
      (by rw [GradedRing.proj_apply]; exact hn₀top n (not_le.mp hc))
  have hzero : ∀ n ∈ (decompose 𝒜 x).support, n ≠ n₀ →
      proj 𝒜 (g + n₀) (r * (decompose 𝒜 x n : A)) = 0 := by
    intro n hn hne
    have hnn₀ : n ≤ n₀ := hle n hn
    rw [_root_.proj_mul_eq 𝒜 r _ n (g + n₀) (SetLike.coe_mem _) (by omega),
      hgtop (g + n₀ - n) (by omega), zero_mul]
  have hexp : proj 𝒜 (g + n₀) (r * x) =
      ∑ n ∈ (decompose 𝒜 x).support, proj 𝒜 (g + n₀) (r * (decompose 𝒜 x n : A)) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x, Finset.mul_sum]
    rw [map_sum]
  by_cases hmem : n₀ ∈ (decompose 𝒜 x).support
  · rw [hexp, Finset.sum_eq_single_of_mem n₀ hmem hzero,
      _root_.proj_mul_eq 𝒜 r _ n₀ (g + n₀) (SetLike.coe_mem _) (Nat.le_add_left n₀ g),
      show g + n₀ - n₀ = g from by omega]
    simp only [GradedRing.proj_apply]
  · have hx0 : proj 𝒜 n₀ x = 0 := by
      by_contra hc
      exact hmem ((GradedRing.mem_support_iff 𝒜 x n₀).mpr hc)
    rw [hexp, hx0, mul_zero]
    exact Finset.sum_eq_zero fun n hn => hzero n hn fun h => hmem (h ▸ hn)

/-- **A prime colon ideal of a homogeneous ideal is homogeneous.** If `I` is a homogeneous ideal of
a nonnegatively graded commutative ring and `p = (I : x) = {r | r * x ∈ I}` is prime for some `x`,
then `p` is homogeneous. -/
theorem isHomogeneous_of_isPrime_colon_singleton {I p : Ideal A}
    (hI : Ideal.IsHomogeneous 𝒜 I) (hp : p.IsPrime) (hpx : ∃ x : A, p = I.colon {x}) :
    Ideal.IsHomogeneous 𝒜 p := by
  classical
  -- `Trimmed c`: some trimmed `x` with `(I : x) = p` has exactly `c` nonzero components.
  set Trimmed : ℕ → Prop := fun c => ∃ x : A, p = I.colon {x} ∧
    (∀ m : ℕ, proj 𝒜 m x ∈ I → proj 𝒜 m x = 0) ∧ (decompose 𝒜 x).support.card = c with hTr
  have hTrne : ∃ c, Trimmed c := by
    obtain ⟨x₀, hx₀⟩ := hpx
    obtain ⟨y, hycol, hy1, hy2⟩ := exists_trimmed_colon_singleton_eq 𝒜 I x₀
    exact ⟨_, y, by rw [hx₀, ← hycol], proj_eq_zero_of_mem_of_trimmed 𝒜 hy1 hy2, rfl⟩
  obtain ⟨x, hxcol, hxtrim, hxcard⟩ := Nat.find_spec hTrne
  have hmin : ∀ y : A, p = I.colon {y} → (∀ m : ℕ, proj 𝒜 m y ∈ I → proj 𝒜 m y = 0) →
      (decompose 𝒜 x).support.card ≤ (decompose 𝒜 y).support.card := by
    intro y hy1 hy2
    rw [hxcard]
    exact Nat.find_min' hTrne ⟨y, hy1, hy2, rfl⟩
  have hcolx : ∀ r : A, r ∈ p ↔ r * x ∈ I := fun r => by
    rw [hxcol, mem_colon_singleton_mul]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((hcolx 1).mpr (by simp)))
  obtain ⟨n₀, hn₀, hn₀top⟩ := exists_top_degree 𝒜 hx0
  have hn₀I : proj 𝒜 n₀ x ∉ I := fun h => hn₀ (hxtrim n₀ h)
  -- Step A: a homogeneous element outside `p` kills no nonzero component of `x` modulo `I`.
  have stepA : ∀ (j : ℕ) (b : A), b ∈ 𝒜 j → b ∉ p → ∀ m : ℕ, proj 𝒜 m x ≠ 0 →
      b * proj 𝒜 m x ∉ I := by
    intro j b hb hbp m hm hcon
    have hmsupp : m ∈ (decompose 𝒜 x).support := (GradedRing.mem_support_iff 𝒜 x m).mpr hm
    have hzcol : p = I.colon {b * x} := by
      refine le_antisymm (fun r hr => ?_) (fun r hr => ?_) <;>
        simp only [mem_colon_singleton_mul] at hr ⊢
      · rw [show r * (b * x) = b * (r * x) from by ring]
        exact I.mul_mem_left _ ((hcolx r).mp hr)
      · refine (hp.mem_or_mem ((hcolx (r * b)).mpr ?_)).resolve_right hbp
        rw [show r * b * x = r * (b * x) from by ring]
        exact hr
    obtain ⟨w, hwcol, hw1, hw2⟩ := exists_trimmed_colon_singleton_eq 𝒜 I (b * x)
    have hsub : (decompose 𝒜 w).support ⊆
        ((decompose 𝒜 x).support.image fun n => j + n).erase (j + m) := by
      intro d hd
      have hdne : proj 𝒜 d w ≠ 0 := (GradedRing.mem_support_iff 𝒜 w d).mp hd
      have hdzI : proj 𝒜 d (b * x) ∉ I := fun hc => hdne (hw1 d hc)
      have hjd : j ≤ d := by
        by_contra hc
        refine hdzI ?_
        rw [show b * x = x * b from mul_comm b x,
          _root_.proj_mul_eq_zero_of_lt 𝒜 x b j d hb (not_le.mp hc)]
        exact I.zero_mem
      obtain ⟨m', rfl⟩ : ∃ m', d = j + m' := ⟨d - j, by omega⟩
      have hval : proj 𝒜 (j + m') (b * x) = b * proj 𝒜 m' x := proj_mul_left_eq 𝒜 hb x m'
      have hm'ne : proj 𝒜 m' x ≠ 0 := fun hc =>
        hdzI (by rw [hval, hc, mul_zero]; exact I.zero_mem)
      refine Finset.mem_erase.mpr ⟨fun hceq => ?_,
        Finset.mem_image.mpr ⟨m', (GradedRing.mem_support_iff 𝒜 x m').mpr hm'ne, rfl⟩⟩
      refine hdzI ?_
      rw [show m' = m from by omega, proj_mul_left_eq 𝒜 hb x m]
      exact hcon
    have hcardlt : (decompose 𝒜 w).support.card < (decompose 𝒜 x).support.card := by
      refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
      rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨m, hmsupp, rfl⟩),
        Finset.card_image_of_injective _ fun a b h => by omega]
      exact Nat.sub_lt (Finset.card_pos.mpr ⟨m, hmsupp⟩) Nat.one_pos
    exact absurd (hmin w (by rw [hzcol, ← hwcol])
      (proj_eq_zero_of_mem_of_trimmed 𝒜 hw1 hw2)) (not_le.mpr hcardlt)
  -- Step B: induction on the number of nonzero components of `r`.
  have stepB : ∀ (c : ℕ) (r : A), (decompose 𝒜 r).support.card ≤ c → r ∈ p →
      ∀ d : ℕ, proj 𝒜 d r ∈ p := by
    intro c
    induction c with
    | zero =>
        intro r hcard _ d
        have hr0 : r = 0 := by
          rw [← DirectSum.sum_support_decompose 𝒜 r,
            Finset.card_eq_zero.mp (Nat.le_zero.mp hcard), Finset.sum_empty]
        rw [hr0, map_zero]
        exact p.zero_mem
    | succ c ih =>
        intro r hcard hrp d
        by_cases hr0 : r = 0
        · rw [hr0, map_zero]
          exact p.zero_mem
        obtain ⟨g, hgne, hgtop⟩ := exists_top_degree 𝒜 hr0
        have hgmem : g ∈ (decompose 𝒜 r).support := (GradedRing.mem_support_iff 𝒜 r g).mpr hgne
        have hgp : proj 𝒜 g r ∈ p := by
          by_contra hc
          refine stepA g (proj 𝒜 g r) (_root_.proj_mem 𝒜 r g) hc n₀ hn₀ ?_
          rw [← proj_mul_top 𝒜 hgtop hn₀top, GradedRing.proj_apply]
          exact hI (g + n₀) ((hcolx r).mp hrp)
        have hgsame : proj 𝒜 g (r - proj 𝒜 g r) = 0 := by
          rw [map_sub, _root_.proj_eq_self_of_mem 𝒜 (_root_.proj_mem 𝒜 r g), sub_self]
        have hgdiff : ∀ e : ℕ, g ≠ e → proj 𝒜 e (r - proj 𝒜 g r) = proj 𝒜 e r := by
          intro e hge
          rw [map_sub, _root_.proj_eq_zero_of_mem_ne 𝒜 (_root_.proj_mem 𝒜 r g) hge, sub_zero]
        have hsub : (decompose 𝒜 (r - proj 𝒜 g r)).support ⊆
            (decompose 𝒜 r).support.erase g := by
          intro e he'
          have hene : proj 𝒜 e (r - proj 𝒜 g r) ≠ 0 := (GradedRing.mem_support_iff 𝒜 _ e).mp he'
          have hge : g ≠ e := fun hc => hene (by rw [← hc]; exact hgsame)
          exact Finset.mem_erase.mpr ⟨fun hc => hge hc.symm,
            (GradedRing.mem_support_iff 𝒜 r e).mpr fun hc => hene (by rw [hgdiff e hge, hc])⟩
        have hcard' : (decompose 𝒜 (r - proj 𝒜 g r)).support.card ≤ c := by
          refine le_trans (Finset.card_le_card hsub) ?_
          rw [Finset.card_erase_of_mem hgmem]
          omega
        have hrec := ih (r - proj 𝒜 g r) hcard' (sub_mem hrp hgp) d
        by_cases hgd : g = d
        · rw [← hgd]
          exact hgp
        · rw [← hgdiff d hgd]
          exact hrec
  intro d r hrp
  rw [← GradedRing.proj_apply]
  exact stepB _ r le_rfl hrp d

/-- **Over a Noetherian graded ring, every associated prime of a homogeneous ideal is
homogeneous.** -/
theorem isHomogeneous_of_mem_associatedPrimes [IsNoetherianRing A] {I p : Ideal A}
    (hI : Ideal.IsHomogeneous 𝒜 I) (hp : p ∈ Submodule.associatedPrimes (I : Submodule A A)) :
    Ideal.IsHomogeneous 𝒜 p := by
  obtain ⟨hprime, x, hx⟩ := Submodule.isAssociatedPrime_iff.mp hp
  exact isHomogeneous_of_isPrime_colon_singleton 𝒜 hI hprime ⟨x, hx⟩

section Saturated

omit [AddSubmonoidClass σ A] [_root_.GradedRing 𝒜] in
/-- **A prime colon ideal of a saturated ideal misses some element of every homogeneous
component.** `I` is *saturated* when an element multiplied into `I` by one whole homogeneous
component already lies in `I`; this is the hypothesis `hsat`. Only the indexed family `𝒜` enters,
not the grading it carries. -/
theorem exists_mem_degree_notMem_of_saturated {I p : Ideal A}
    (hsat : ∀ x : A, (∃ N : ℕ, ∀ y : A, y ∈ 𝒜 N → y * x ∈ I) → x ∈ I)
    (hp : p.IsPrime) (hpx : ∃ x : A, p = I.colon {x}) (N : ℕ) :
    ∃ y : A, y ∈ 𝒜 N ∧ y ∉ p := by
  obtain ⟨x, hx⟩ := hpx
  have hcol : ∀ r : A, r ∈ p ↔ r * x ∈ I := fun r => by
    rw [hx, mem_colon_singleton_mul]
  by_contra hc
  have hall : ∀ y : A, y ∈ 𝒜 N → y * x ∈ I := by
    intro y hy
    by_contra hyx
    exact hc ⟨y, hy, fun hyp => hyx ((hcol y).mp hyp)⟩
  refine hp.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)
  rw [hcol 1, one_mul]
  exact hsat x ⟨N, hall⟩

/-- **The irrelevant ideal is not contained in any prime colon ideal of a saturated ideal.** In
particular the irrelevant ideal is itself not of that form. The degree-one part already witnesses
this, so no hypothesis of generation in degree one is needed. -/
theorem not_irrelevant_le_of_saturated {I p : Ideal A}
    (hsat : ∀ x : A, (∃ N : ℕ, ∀ y : A, y ∈ 𝒜 N → y * x ∈ I) → x ∈ I)
    (hp : p.IsPrime) (hpx : ∃ x : A, p = I.colon {x}) :
    ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p := by
  obtain ⟨y, hy1, hyp⟩ := exists_mem_degree_notMem_of_saturated 𝒜 hsat hp hpx 1
  exact fun hle => hyp (hle (_root_.mem_irrelevant_of_mem_of_pos 𝒜 hy1 Nat.one_pos))

/-- **Over a Noetherian graded ring, no associated prime of a saturated ideal contains the
irrelevant ideal.** -/
theorem not_irrelevant_le_of_mem_associatedPrimes_of_saturated [IsNoetherianRing A]
    {I p : Ideal A} (hsat : ∀ x : A, (∃ N : ℕ, ∀ y : A, y ∈ 𝒜 N → y * x ∈ I) → x ∈ I)
    (hp : p ∈ Submodule.associatedPrimes (I : Submodule A A)) :
    ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p := by
  obtain ⟨hprime, x, hx⟩ := Submodule.isAssociatedPrime_iff.mp hp
  exact not_irrelevant_le_of_saturated 𝒜 hsat hprime ⟨x, hx⟩

/-- **The associated primes of a saturated homogeneous ideal over a Noetherian graded ring are
homogeneous and relevant.** This is the form the `Proj` application consumes: each associated prime
is a homogeneous prime not containing the irrelevant ideal, hence a point of `Proj 𝒜`. -/
theorem isHomogeneous_and_not_irrelevant_le_of_mem_associatedPrimes [IsNoetherianRing A]
    {I p : Ideal A} (hI : Ideal.IsHomogeneous 𝒜 I)
    (hsat : ∀ x : A, (∃ N : ℕ, ∀ y : A, y ∈ 𝒜 N → y * x ∈ I) → x ∈ I)
    (hp : p ∈ Submodule.associatedPrimes (I : Submodule A A)) :
    Ideal.IsHomogeneous 𝒜 p ∧ ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p :=
  ⟨isHomogeneous_of_mem_associatedPrimes 𝒜 hI hp,
    not_irrelevant_le_of_mem_associatedPrimes_of_saturated 𝒜 hsat hp⟩

end Saturated

end Stacks.GradedRing

end
