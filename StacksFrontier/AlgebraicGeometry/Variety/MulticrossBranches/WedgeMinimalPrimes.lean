module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Branches.Wedge

/-!
# The minimal primes of a wedge of discrete valuation rings

A wedge of a nonempty finite family of discrete valuation rings has exactly one minimal prime
for each factor.

## Main definitions

* `IsLocalRing.wedgeProjection` is the coordinate projection of a wedge onto one of its factors.

## Main results

* `IsLocalRing.wedgeProjection_surjective` says every element of a factor is a coordinate of an
  element of the wedge: the other coordinates can be chosen with the prescribed residue.
* `IsLocalRing.encard_minimalPrimes_wedgeSubring` counts the minimal primes of a wedge of
  discrete valuation rings.

## Implementation notes

The minimal primes are exactly the kernels of the coordinate projections.  That they are prime
is immediate; that they are minimal and exhaust the minimal primes both come from the fact that
their infimum is `⊥`, because an element of the wedge killed by every projection is zero.  They
are pairwise distinct because a uniformizer of one factor, extended by zero, lies in every other
kernel and not in its own — this is where the factors being discrete valuation rings, rather
than arbitrary local rings, is used: it supplies a nonzero element of the maximal ideal.

## References

* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
-/

@[expose] public noncomputable section

open IsLocalRing

universe v

namespace IsLocalRing

/-- The projection of a wedge of local rings onto one of its factors. -/
def wedgeProjection {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+*
      ResidueField (B (Fin.last n))) (i : Fin (n + 1)) :
    wedgeSubring B e →+* B i :=
  { toFun := fun x => x.1 i
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

/-- The kernel of a coordinate projection of a wedge. -/
def wedgeProjectionKernel {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+*
      ResidueField (B (Fin.last n))) (i : Fin (n + 1)) :
    Ideal (wedgeSubring B e) :=
  RingHom.ker (wedgeProjection B e i)

/-- A choice of lift of an element of the residue field. -/
private def residueLift {R : Type*} [CommRing R] [IsLocalRing R]
    (x : ResidueField R) : R := Classical.choose (residue_surjective x)

private theorem residue_residueLift {R : Type*} [CommRing R] [IsLocalRing R]
    (x : ResidueField R) : residue R (residueLift x) = x :=
  Classical.choose_spec (residue_surjective x)

/-- Every element of a factor is the corresponding coordinate of an element of the wedge: the
other coordinates are chosen as lifts of the residue dictated by the identifications. -/
theorem wedgeProjection_surjective
    {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+*
      ResidueField (B (Fin.last n))) (i : Fin (n + 1)) :
    Function.Surjective (wedgeProjection B e i) := by
  intro b
  induction i using Fin.lastCases with
  | last =>
      let r := residue (B (Fin.last n)) b
      let f : ∀ l, B l := Fin.lastCases b (fun j => residueLift ((e j).symm r))
      have hf : f ∈ wedgeSubring B e := by
        rw [mem_wedgeSubring]
        intro j
        simp [f, r, residue_residueLift]
      refine ⟨⟨f, hf⟩, ?_⟩
      simp [wedgeProjection, f]
  | cast j =>
      let r := e j (residue (B j.castSucc) b)
      let f : ∀ l, B l := Fin.lastCases (residueLift r) fun l =>
        if h : l = j then h ▸ b else residueLift ((e l).symm r)
      have hf : f ∈ wedgeSubring B e := by
        rw [mem_wedgeSubring]
        intro l
        by_cases h : l = j
        · subst l
          simp [f, r, residue_residueLift]
        · simp [f, h, r, residue_residueLift]
      refine ⟨⟨f, hf⟩, ?_⟩
      simp [wedgeProjection, f]

/-- A uniformizer of one factor, extended by zero, separates that factor's kernel from any
other. -/
private theorem exists_mem_wedgeProjectionKernel_not
    {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsDiscreteValuationRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+*
      ResidueField (B (Fin.last n))) {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∃ x : wedgeSubring B e,
      x ∈ wedgeProjectionKernel B e j ∧ x ∉ wedgeProjectionKernel B e i := by
  have hmax : maximalIdeal (B i) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (B i)
      ((isField_iff_maximalIdeal_eq).mpr h)
  obtain ⟨a, ha, ha0⟩ := (maximalIdeal (B i)).ne_bot_iff.mp hmax
  let f : ∀ l, B l := fun l => if h : l = i then h ▸ a else 0
  have hfres (l : Fin (n + 1)) : residue (B l) (f l) = 0 := by
    by_cases h : l = i
    · subst l
      simp [f, ha]
    · simp [f, h]
  have hf : f ∈ wedgeSubring B e := by
    rw [mem_wedgeSubring]
    intro l
    simp [hfres]
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · change f j = 0
    simp [f, hij.symm]
  · change f i ≠ 0
    simpa [f] using ha0

/-- **A wedge of `n + 1` discrete valuation rings has `n + 1` minimal primes.**  They are the
kernels of the coordinate projections. -/
theorem encard_minimalPrimes_wedgeSubring
    {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsDiscreteValuationRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+*
      ResidueField (B (Fin.last n))) :
    (minimalPrimes (wedgeSubring B e)).encard = (n + 1 : ℕ∞) := by
  let P := wedgeProjectionKernel B e
  have hprime (i : Fin (n + 1)) : (P i).IsPrime := RingHom.ker_isPrime _
  have hinf : Finset.univ.inf P = (⊥ : Ideal (wedgeSubring B e)) := by
    refine bot_unique (fun x hx => Subtype.ext (funext fun i => ?_))
    have hxi : x ∈ P i := (Finset.inf_le (Finset.mem_univ i) : Finset.univ.inf P ≤ P i) hx
    simpa [P, wedgeProjection] using RingHom.mem_ker.mp hxi
  have hex (q : Ideal (wedgeSubring B e)) (hq : q.IsPrime) : ∃ i, P i ≤ q := by
    obtain ⟨i, -, hi⟩ := hq.inf_le'.mp (hinf.le.trans bot_le)
    exact ⟨i, hi⟩
  have hminimal (i : Fin (n + 1)) : P i ∈ minimalPrimes (wedgeSubring B e) := by
    refine ⟨⟨hprime i, bot_le⟩, fun q hq hqi => ?_⟩
    obtain ⟨j, hj⟩ := hex q hq.1
    by_cases hji : j = i
    · exact hji ▸ hj
    · obtain ⟨x, hxj, hxi⟩ :=
        exists_mem_wedgeProjectionKernel_not (B := B) (e := e) (Ne.symm hji)
      exact (hxi (hqi (hj hxj))).elim
  have hrange : minimalPrimes (wedgeSubring B e) = Set.range P := by
    refine Set.Subset.antisymm (fun q hq => ?_) (Set.range_subset_iff.2 hminimal)
    obtain ⟨i, hi⟩ := hex q hq.1.1
    exact ⟨i, le_antisymm hi (hq.2 ⟨hprime i, bot_le⟩ hi)⟩
  have hPinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    obtain ⟨x, hxj, hxi⟩ := exists_mem_wedgeProjectionKernel_not (B := B) (e := e) hne
    exact hxi (hij.ge hxj)
  calc
    (minimalPrimes (wedgeSubring B e)).encard = (Set.range P).encard :=
      congrArg Set.encard hrange
    _ = (P '' (Set.univ : Set (Fin (n + 1)))).encard := by rw [Set.image_univ]
    _ = (Set.univ : Set (Fin (n + 1))).encard := hPinj.encard_image _
    _ = (n + 1 : ℕ∞) := by simp

end IsLocalRing

end
