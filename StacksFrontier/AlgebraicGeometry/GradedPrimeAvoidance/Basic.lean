module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover

/-!
# Graded prime avoidance over a finite set of primes

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded commutative ring and let `p₁, …, p_r` be prime ideals of `A`,
each of which omits some homogeneous element of positive degree. Then **one** homogeneous element
of positive degree omits all of them at once.

Geometrically: a finite set of points of `Proj 𝒜` is contained in a single standard open `D₊(f)`
of a homogeneous `f` of positive degree. This is the step by which [Stacks, Tag 0E21] and
[Stacks, Tag 09NV] pass from finitely many points of a projective space to a single homogeneous
polynomial, whose evaluation at the sections defining the morphism to that projective space is
the section of a tensor power the tags produce.

## Main results

* `Stacks.GradedRing.exists_homogeneous_pos_notMem_finset`: **graded prime avoidance.** Given a
  finite nonempty family of prime ideals, each omitting a homogeneous element of positive degree,
  there is a single homogeneous element of positive degree omitted by all of them.
* `Stacks.AlgebraicGeometry.ProjShared.exists_notMem_asHomogeneousIdeal_of_finite` and
  `Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_pos_superset`: a finite
  nonempty set of points of `Proj 𝒜` lies in a single `D₊(f)` with `f` homogeneous of positive
  degree.

## Implementation notes

Mathlib has ungraded prime avoidance (`Ideal.subset_union_prime`) but nothing graded, and the
ungraded statement does not give the graded one: an element of the irrelevant ideal outside every
`p i` has, for each `i`, *some* homogeneous component outside `p i`, and the component may depend
on `i`. The proof here is the classical one and is run directly.

Strong induction on the cardinality of the index set. For a single prime the hypothesis is the
conclusion. For `r ≥ 2`, the induction hypothesis applied to each `s.erase i` — which is nonempty
because `r ≥ 2` — gives a homogeneous `yᵢ` of positive degree `dᵢ` omitted by every `p j` with
`j ≠ i`. If some `yᵢ` is also omitted by `p i` we are done. Otherwise `yᵢ ∈ p i` for every `i`,
and the witness is the "Vandermonde sum"

  `x = ∑ᵢ ∏_{j ≠ i} z j`,   `z i = yᵢ ^ (∏_{j ≠ i} d j)`,

whose terms all have degree `(r - 1) · D` with `D = ∏ⱼ dⱼ`, so that `x` is homogeneous. The
exponents are what make the degrees agree, and raising to a positive power preserves both
membership and non-membership in a prime. Modulo `p i` every term but the `i`-th vanishes,
because it has `z i ∈ p i` as a factor, while the `i`-th is a product of elements outside the
prime `p i`, hence outside it. The degree `(r - 1) · D` is positive exactly because `r ≥ 2`,
which is why the one-prime case has to be peeled off first.

The grading is a family `𝒜 : ℕ → σ` in a `SetLike` type with `AddSubgroupClass σ A`, the
generality of Mathlib's `Proj` and of
`StacksFrontier/AlgebraicGeometry/ProjShared/RelevantCover.lean`, whose
`Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem` is the one-point case the
geometric corollary feeds in.

The nonemptiness hypothesis cannot be dropped: if `𝒜 n` is trivial for every `n > 0` there is no
homogeneous element of positive degree at all, and the conclusion fails for the empty family.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
-/

@[expose] public section

open AlgebraicGeometry Finset

universe u w

namespace Stacks.GradedRing

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Graded prime avoidance.** Let `A` be a graded commutative ring and let `p i`, for `i` in a
finite nonempty index set `s`, be prime ideals of `A`, each omitting some homogeneous element of
positive degree. Then there is a single homogeneous element of positive degree lying outside
every `p i`.

Mathlib's `Ideal.subset_union_prime` is the ungraded statement and does not imply this one; see
the implementation notes. -/
public theorem exists_homogeneous_pos_notMem_finset {ι : Type*} (p : ι → Ideal A)
    (s : Finset ι) :
    s.Nonempty → (∀ i ∈ s, (p i).IsPrime) →
      (∀ i ∈ s, ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ f ∉ p i) →
      ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ ∀ i ∈ s, f ∉ p i := by
  classical
  induction s using Finset.strongInduction with
  | _ s IH =>
  intro hs hp h
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  by_cases hcard : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨n, f, hn, hf, hfp⟩ := h i (by simp)
    exact ⟨n, f, hn, hf, by simpa using hfp⟩
  have h2 : 2 ≤ s.card := by omega
  have key : ∀ i ∈ s, ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ ∀ j ∈ s.erase i, f ∉ p j := by
    intro i hi
    refine IH (s.erase i) (Finset.erase_ssubset hi) ?_
      (fun j hj => hp j (Finset.mem_of_mem_erase hj))
      (fun j hj => h j (Finset.mem_of_mem_erase hj))
    rw [← Finset.card_pos, Finset.card_erase_of_mem hi]
    omega
  choose! d y hdpos hymem hynot using key
  by_cases hgood : ∃ i ∈ s, y i ∉ p i
  · obtain ⟨i, hi, hyi⟩ := hgood
    refine ⟨d i, y i, hdpos i hi, hymem i hi, fun j hj => ?_⟩
    by_cases hji : j = i
    · exact hji ▸ hyi
    · exact hynot i hi j (Finset.mem_erase.mpr ⟨hji, hj⟩)
  simp only [not_exists, not_and, not_not] at hgood
  set D : ℕ := ∏ j ∈ s, d j with hD
  have hDpos : 0 < D := Finset.prod_pos fun j hj => hdpos j hj
  set k : ι → ℕ := fun i => ∏ j ∈ s.erase i, d j with hk
  have hkpos : ∀ i ∈ s, 0 < k i := fun i hi =>
    Finset.prod_pos fun j hj => hdpos j (Finset.mem_of_mem_erase hj)
  set z : ι → A := fun i => y i ^ k i with hz
  have hzmem : ∀ i ∈ s, z i ∈ 𝒜 D := by
    intro i hi
    have hDi : d i * k i = D := by
      rw [hk, hD]
      exact Finset.mul_prod_erase s d hi
    have hmem := SetLike.pow_mem_graded (A := 𝒜) (k i) (hymem i hi)
    rw [smul_eq_mul, mul_comm] at hmem
    rwa [hDi] at hmem
  have hzin : ∀ i ∈ s, z i ∈ p i := fun i hi =>
    Ideal.pow_mem_of_mem _ (hgood i hi) _ (hkpos i hi)
  have hznot : ∀ i ∈ s, ∀ j ∈ s.erase i, z i ∉ p j := by
    intro i hi j hj
    have hpj := hp j (Finset.mem_of_mem_erase hj)
    exact fun hc => hynot i hi j hj (hpj.mem_of_pow_mem _ hc)
  have hswap : ∀ i ∈ s, ∀ m ∈ s.erase i, i ∈ s.erase m := by
    simp +contextual [eq_comm]
  refine ⟨(s.card - 1) * D, ∑ i ∈ s, ∏ j ∈ s.erase i, z j, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (by omega) hDpos
  · refine sum_mem fun i hi => ?_
    have hprod := SetLike.prod_mem_graded 𝒜 (fun _ : ι => D) z
      (F := s.erase i) (fun j hj => hzmem j (Finset.mem_of_mem_erase hj))
    rwa [Finset.sum_const, Finset.card_erase_of_mem hi, smul_eq_mul] at hprod
  · intro i hi hc
    have hpi := hp i hi
    have hrest : ∑ m ∈ s.erase i, ∏ j ∈ s.erase m, z j ∈ p i := by
      refine Ideal.sum_mem _ fun m hm => ?_
      rw [← Finset.mul_prod_erase _ z (hswap i hi m hm)]
      exact Ideal.mul_mem_right _ _ (hzin i hi)
    have hterm : ∏ j ∈ s.erase i, z j ∈ p i := by
      have hsplit := Finset.add_sum_erase s (fun i => ∏ j ∈ s.erase i, z j) hi
      exact (Ideal.add_mem_iff_left _ hrest).mp (hsplit ▸ hc)
    obtain ⟨j, hj, hjp⟩ := Ideal.IsPrime.prod_mem_iff.mp hterm
    exact hznot j (Finset.mem_of_mem_erase hj) i (hswap i hi j hj) hjp

end Stacks.GradedRing

namespace Stacks.AlgebraicGeometry.ProjShared

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite nonempty set of points of `Proj 𝒜` omits a single homogeneous element of positive
degree: graded prime avoidance applied to the homogeneous primes of the points, whose
one-point case is
`Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem`. -/
public theorem exists_notMem_asHomogeneousIdeal_of_finite {E : Set (Proj 𝒜)}
    (hE : E.Finite) (hne : E.Nonempty) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ ∀ x ∈ E, f ∉ x.asHomogeneousIdeal := by
  classical
  obtain ⟨n, f, hn, hf, hfp⟩ :=
    Stacks.GradedRing.exists_homogeneous_pos_notMem_finset 𝒜
      (fun x : Proj 𝒜 => x.asHomogeneousIdeal.toIdeal) hE.toFinset
      (by simpa using hne) (fun x _ => x.isPrime)
      (fun x _ => exists_homogeneous_pos_notMem 𝒜 x)
  exact ⟨n, f, hn, hf, fun x hx => hfp x (hE.mem_toFinset.mpr hx)⟩

/-- **A finite nonempty set of points of `Proj 𝒜` is contained in a single standard open `D₊(f)`
with `f` homogeneous of positive degree.** -/
public theorem exists_basicOpen_homogeneous_pos_superset {E : Set (Proj 𝒜)}
    (hE : E.Finite) (hne : E.Nonempty) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ E ⊆ Proj.basicOpen 𝒜 f := by
  obtain ⟨n, f, hn, hf, hfp⟩ := exists_notMem_asHomogeneousIdeal_of_finite 𝒜 hE hne
  exact ⟨n, f, hn, hf, fun x hx => hfp x hx⟩

end Stacks.AlgebraicGeometry.ProjShared

end
