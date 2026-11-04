module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Graded prime avoidance

Let `S` be an `ℕ`-graded commutative ring, let `𝔭 i` for `i` in a finite set be homogeneous
prime ideals of `S`, and let `I` be a homogeneous ideal contained in the irrelevant ideal `S₊`
with `I` contained in none of the `𝔭 i`. Then `I` contains a homogeneous element of positive
degree lying outside every `𝔭 i`.

This is the graded analogue of prime avoidance (Stacks, Algebra, Lemma 10.57.6 — tag 00JS), the
graded counterpart of the ungraded `Ideal.subset_union_prime`. It is the second half of the
infrastructure that the ample-sheaf arguments of Stacks Chapter "Properties of Schemes" need:
applied to the graded ring `Γ_*(X, L)` of Stacks Tag 01CV, it produces the homogeneous section
of some positive power of `L` whose nonvanishing locus meets each of finitely many prescribed
points.

## Main results

* `Stacks.GradedAvoidance.exists_homogeneous_pos_notMem`: the one-ideal case, which is also the
  engine of the induction. Primality is not needed for it.
* `Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem`: **graded prime avoidance.**

## Implementation notes

**Where the positivity of the degree comes from.** Not from an extra argument: a homogeneous
element of `I` of degree `0` lies in `I ⊓ 𝒜 0`, and `I ≤ S₊` forces that to be `0`, which is in
every ideal. So the one-ideal case may simply discard the degree-`0` component, and the
hypothesis `I ≤ S₊` is used nowhere else. That case needs no primality at all — a homogeneous
ideal not inside an arbitrary ideal has a homogeneous element of positive degree outside it —
which is slightly stronger than the source states and is what the inductive step consumes.

**The inclusion among the primes, and how it is handled.** The source's proof opens with "we
may assume there are no inclusions among the `𝔭 i`", and that reduction is the only subtle point:
the step needs `I * 𝔭 1 * ⋯ * 𝔭 (r-1) ⊄ 𝔭 r`, and primality of `𝔭 r` returns either
`I ≤ 𝔭 r` — excluded by hypothesis — or `𝔭 i ≤ 𝔭 r` for some earlier `i`, which an inclusion
would permit. Rather than prune the family to an antichain, the proof below **chooses `r` to be
minimal** for inclusion among `{𝔭 i : i ∈ s}` (`Finset.exists_minimalFor`). Then
`𝔭 i ≤ 𝔭 r` for an `i` of the smaller family forces `𝔭 r ≤ 𝔭 i`, and the element already
produced for the smaller family lies inside `𝔭 r` and outside `𝔭 i` — a contradiction, with no
pruning anywhere. The induction is then a plain strong induction on the finite set,
with the ideal `I` quantified inside, since the inductive step applies the one-prime case to a
different ideal.

**Products of ideals.** `Ideal.mul_le_left` carries an `IsTwoSided` side condition, so the
product is always formed with the factor to be discarded on the **left** and
`Ideal.mul_le_inf` is used for the other containment; no two-sidedness instance is needed.

**Generality.** Stated on Mathlib's `SetLike`/`AddSubgroupClass` graded interface — so it
applies to an internal grading by submodules, by additive subgroups, or by any carrier — with
the ring, the carrier and the index type of the family in independent universes. The grading is
by `ℕ`; the irrelevant ideal is only defined for a canonically ordered index, and "positive
degree" is an `ℕ` statement.

## References

* [Stacks Project, Tag 00JS](https://stacks.math.columbia.edu/tag/00JS)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS) — the ungraded
  statement, which Mathlib has as `Ideal.subset_union_prime`.

## What is not done

Nothing is deduced about the homogeneous spectrum: the statement is not restated in terms of
`ProjectiveSpectrum` or of `AlgebraicGeometry.Proj.basicOpen`, although the intended
consequence — that finitely many points of `Proj` all missed by `I` are simultaneously missed by
a single homogeneous element of `I` of positive degree — is immediate from it.
-/

@[expose] public section

open DirectSum

namespace Stacks.GradedAvoidance

variable {ι : Type*} {σ : Type*} {A : Type*} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A homogeneous ideal inside the irrelevant ideal has no nonzero element of degree zero. -/
theorem eq_zero_of_mem_graded_zero {I : Ideal A}
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {x : A} (hx : x ∈ 𝒜 0)
    (hxI : x ∈ I) : x = 0 := by
  have := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mp (hI hxI)
  rwa [GradedRing.proj_apply, decompose_of_mem_same 𝒜 hx] at this

/-- **Graded avoidance of a single ideal.** A homogeneous ideal inside the irrelevant ideal and
not inside an ideal `P` contains a homogeneous element of positive degree outside `P`. This is
also the engine of the general case; note that `P` need not be prime, which is why the general
case can apply it to the ideal `P` it is currently correcting at. -/
theorem exists_homogeneous_pos_notMem {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (hIrr : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {P : Ideal A}
    (hne : ¬ I ≤ P) : ∃ (d : ℕ) (x : A), 0 < d ∧ x ∈ 𝒜 d ∧ x ∈ I ∧ x ∉ P := by
  classical
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp hne
  -- some homogeneous component of `f` is outside `P`
  by_contra hcon
  refine hfP ?_
  rw [← sum_support_decompose 𝒜 f]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    rw [eq_zero_of_mem_graded_zero 𝒜 hIrr (decompose 𝒜 f 0).2 (hI 0 hfI)]
    exact P.zero_mem
  · by_contra hmem
    exact hcon ⟨d, (decompose 𝒜 f d : A), Nat.pos_of_ne_zero hd, (decompose 𝒜 f d).2,
      hI d hfI, hmem⟩

/-- A finite product of homogeneous ideals is homogeneous. -/
theorem isHomogeneous_prod (s : Finset ι) (𝔭 : ι → Ideal A)
    (h : ∀ i ∈ s, (𝔭 i).IsHomogeneous 𝒜) : (∏ i ∈ s, 𝔭 i).IsHomogeneous 𝒜 := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Ideal.IsHomogeneous.top 𝒜
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A factor of a finite product of ideals contains it. -/
theorem prod_le_of_mem {s : Finset ι} (𝔭 : ι → Ideal A) {j : ι} (hj : j ∈ s) :
    ∏ i ∈ s, 𝔭 i ≤ 𝔭 j := by
  classical
  rw [← Finset.prod_erase_mul _ _ hj]
  exact Ideal.mul_le_inf.trans inf_le_right

/-- In a prime ideal `P`, if `a ∈ P` and `a ^ m + b ^ n ∈ P` with `0 < m`, `0 < n`, then `b ∈ P`. -/
private theorem mem_of_mem_of_add_pow_mem {P : Ideal A} (hP : P.IsPrime) {a b : A} {m n : ℕ}
    (ha : a ∈ P) (hm : 0 < m) (hn : 0 < n) (h : a ^ m + b ^ n ∈ P) : b ∈ P :=
  (hP.pow_mem_iff_mem n hn).mp (by simpa using Ideal.sub_mem _ h (Ideal.pow_mem_of_mem _ ha _ hm))

/-- **Graded prime avoidance.** Stacks, Algebra, Lemma 10.57.6: a homogeneous ideal `I` inside
the irrelevant ideal and inside none of finitely many homogeneous prime ideals contains a
homogeneous element of positive degree outside all of them.

The ideal `I` is quantified inside the statement because the inductive step applies the
one-prime case to the product of `I` with the remaining primes. -/
theorem exists_homogeneous_pos_forall_notMem (𝔭 : ι → Ideal A) :
    ∀ (s : Finset ι), (∀ i ∈ s, (𝔭 i).IsHomogeneous 𝒜) → (∀ i ∈ s, (𝔭 i).IsPrime) →
      ∀ (I : Ideal A), I.IsHomogeneous 𝒜 → I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
        (∀ i ∈ s, ¬ I ≤ 𝔭 i) →
        ∃ (d : ℕ) (x : A), 0 < d ∧ x ∈ 𝒜 d ∧ x ∈ I ∧ ∀ i ∈ s, x ∉ 𝔭 i := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hhom hprime I hI hIrr hne
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨1, 0, Nat.one_pos, zero_mem _, I.zero_mem, by simp⟩
    -- choose `r` with `𝔭 r` minimal among the family
    obtain ⟨r, hrs, hrmin⟩ := Finset.exists_minimalFor 𝔭 s hs
    have hsub : s.erase r ⊂ s := Finset.erase_ssubset hrs
    have hmem' : ∀ i ∈ s.erase r, i ∈ s := fun i hi => Finset.mem_of_mem_erase hi
    obtain ⟨d, x, hd, hxd, hxI, hx⟩ := ih _ hsub (fun i hi => hhom i (hmem' i hi))
      (fun i hi => hprime i (hmem' i hi)) I hI hIrr (fun i hi => hne i (hmem' i hi))
    by_cases hxr : x ∈ 𝔭 r
    · -- `x` fails only at `r`; correct it by adding a suitable element of `I * ∏ 𝔭 i`
      set J : Ideal A := (∏ i ∈ s.erase r, 𝔭 i) * I with hJ
      have hJI : J ≤ I := Ideal.mul_le_right
      have hJprod : J ≤ ∏ i ∈ s.erase r, 𝔭 i := Ideal.mul_le_inf.trans inf_le_left
      have hJhom : J.IsHomogeneous 𝒜 :=
        (isHomogeneous_prod 𝒜 _ 𝔭 fun i hi => hhom i (hmem' i hi)).mul hI
      have hJr : ¬ J ≤ 𝔭 r := by
        intro hle
        rcases (hprime r hrs).mul_le.mp hle with hle' | hle'
        · obtain ⟨i, hi, hile⟩ := (hprime r hrs).prod_le.mp hle'
          exact hx i hi (hrmin (hmem' i hi) hile hxr)
        · exact hne r hrs hle'
      obtain ⟨e, y, he, hye, hyJ, hyr⟩ :=
        exists_homogeneous_pos_notMem 𝒜 hJhom (hJI.trans hIrr) hJr
      refine ⟨d * e, x ^ e + y ^ d, Nat.mul_pos hd he, ?_, ?_, ?_⟩
      · refine add_mem ?_ ?_
        · simpa [Nat.mul_comm, smul_eq_mul] using SetLike.pow_mem_graded e hxd
        · simpa [smul_eq_mul] using SetLike.pow_mem_graded d hye
      · exact add_mem (Ideal.pow_mem_of_mem _ hxI _ he) (Ideal.pow_mem_of_mem _ (hJI hyJ) _ hd)
      · intro i hi hz
        by_cases hir : i = r
        · subst hir
          exact hyr (mem_of_mem_of_add_pow_mem (hprime i hi) hxr he hd hz)
        · have hiJ : y ∈ 𝔭 i :=
            prod_le_of_mem 𝔭 (Finset.mem_erase.mpr ⟨hir, hi⟩) (hJprod hyJ)
          exact hx i (Finset.mem_erase.mpr ⟨hir, hi⟩)
            (mem_of_mem_of_add_pow_mem (hprime i hi) hiJ hd he (by rwa [add_comm] at hz))
    · exact ⟨d, x, hd, hxd, hxI, fun i hi => by
        by_cases hir : i = r
        · exact hir ▸ hxr
        · exact hx i (Finset.mem_erase.mpr ⟨hir, hi⟩)⟩

end Stacks.GradedAvoidance
