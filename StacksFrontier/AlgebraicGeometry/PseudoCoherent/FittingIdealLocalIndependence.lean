module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealMinimalComparison

/-!
# The Fitting ideals of a complex of finite free modules over a local ring do not depend on it

Let `R` be a local ring and let `C₁`, `C₂` be bounded-above complexes of finite free `R`-modules,
recorded as `Stacks.FittingComplex.FreeData`. If the two are isomorphic in the derived category
`D(R)` then they have the same Fitting ideals, in every degree and at every index. This is the
whole content of the proof of [Stacks, Tag 0ESP], carried out over a local ring, which is where
the source carries it out.

The source proves it in two halves, and so does this file.

* **Splitting.** While some differential of the complex has a unit matrix entry in a degree above
  the one being computed, [Stacks, Tag 00MT] splits off a trivial two-term complex. That changes
  neither the Fitting ideals
  (`Stacks.FittingComplex.FreeData.exists_freeData_fittingIdeal_eq_of_isUnit`) nor the homotopy
  type, and it strictly decreases the sum of the ranks in the degrees above the cutoff, which is
  finite because the ranks vanish above `top`. So the complex may be assumed *minimal above the
  cutoff*: every entry of every differential there lies in the maximal ideal. This is
  `Stacks.FittingComplex.FreeData.exists_minimal_above`.
* **Uniqueness.** Two minimal complexes that are homotopy equivalent agree above the cutoff up to
  a degreewise invertible change of basis, by Nakayama's lemma. This is
  `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_matrixHtpy_of_minimal`.

## Main results

* `Stacks.FittingComplex.FreeData.exists_minimal_above`: the splitting half.
* `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_matrixHtpy`: the two halves combined — two
  homotopy equivalent bounded-above complexes of finite free modules over a local ring have the
  same Fitting ideals.
* `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_derivedIso`: the same with the hypothesis
  read in the derived category, which is the form in which the local description of
  [Stacks, Tag 0ESP] supplies it.

## Implementation notes

The homotopy equivalence is carried as the matrix data
`Stacks.FittingComplex.FreeData.MatrixHtpy` rather than as a `HomotopyEquiv` of the cochain
complexes, because the splitting step transports it twice — along the degreewise invertible change
of basis of [Stacks, Tag 00MT] and across the cancellation of the trivial summand — and both
transports are computations with block matrices. The passage from an isomorphism of `D(R)` to that
data happens once, at the end, through the K-projectivity of a bounded-above complex of finite
free modules.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

open CategoryTheory Matrix

namespace Stacks.FittingComplex.FreeData

universe u w

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Splitting off trivial two-term complexes until the complex is minimal above `c`.**

The resulting complex has the same Fitting ideals, is still related to whatever the given one was
related to, and has every entry of every differential in degrees `≥ c` inside the maximal ideal.
The recursion is on the sum of the ranks in the degrees between `c` and a bound above which they
vanish: splitting off a trivial two-term complex in a degree `≥ c` decrements two of them. -/
theorem exists_minimal_above (c B : ℤ) :
    ∀ (m : ℕ) (C : FreeData R) (_ : ∀ i : ℤ, C.d (i + 1) * C.d i = 0)
      (_ : ∀ j : ℤ, B < j → C.rank j = 0) (_ : ∑ j ∈ Finset.Icc c B, C.rank j = m)
      (Z : FreeData R) (_ : MatrixHtpy C Z),
      ∃ C' : FreeData R, (∀ i : ℤ, C'.d (i + 1) * C'.d i = 0) ∧
        (∀ p k : ℤ, C'.fittingIdeal p k = C.fittingIdeal p k) ∧
        (∀ i : ℤ, c ≤ i → ∀ a b, C'.d i a b ∈ IsLocalRing.maximalIdeal R) ∧
        Nonempty (MatrixHtpy C' Z) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro C hdd hB hm Z e
    by_cases hmin : ∀ i : ℤ, c ≤ i → ∀ a b, C.d i a b ∈ IsLocalRing.maximalIdeal R
    · exact ⟨C, hdd, fun _ _ => rfl, hmin, ⟨e⟩⟩
    · push Not at hmin
      obtain ⟨i, hi, a, b, hab⟩ := hmin
      have hu : IsUnit (C.d i a b) := by
        by_contra hc
        exact hab ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hc))
      obtain ⟨hri, hri1, C', hrank, hdd', hfit, P, Q, hPQ, hQP, hconj⟩ :=
        exists_freeData_fittingIdeal_eq_of_isUnit C hdd a b hu
      -- the ranks of the reduced complex do not exceed those of `C`, and are smaller at `i`
      have hle : ∀ j : ℤ, C'.rank j ≤ C.rank j := by
        intro j
        rw [hrank j]
        split_ifs with h1 h2
        · subst h1; omega
        · subst h2; omega
        · exact le_rfl
      have hiB : i + 1 ≤ B := by
        by_contra hcon
        rw [hB (i + 1) (by omega)] at hri1
        omega
      have hmemi : i ∈ Finset.Icc c B := Finset.mem_Icc.mpr ⟨hi, by omega⟩
      have hlt : ∑ j ∈ Finset.Icc c B, C'.rank j < m := by
        rw [← hm]
        refine Finset.sum_lt_sum (fun j _ => hle j) ⟨i, hmemi, ?_⟩
        rw [hrank i, ite_eq_left rfl]
        omega
      have hB' : ∀ j : ℤ, B < j → C'.rank j = 0 := fun j hj =>
        Nat.eq_zero_of_le_zero ((hle j).trans_eq (hB j hj))
      -- transport the data along the change of basis, then cancel the trivial summand
      have e' : MatrixHtpy (C'.directSum (trivialComplex R i 1)) Z :=
        MatrixHtpy.ofConj e P Q hPQ hQP hconj
      have e'' : MatrixHtpy C' Z :=
        MatrixHtpy.ofDirectSum C' (trivialComplex R i 1) Z e'.toMat e'.invMat e'.htpy₁ e'.htpy₂
          e'.toMat_comm e'.invMat_comm e'.invMat_toMat e'.toMat_invMat
          (trivialContr i 1) (trivialContr_spec i 1)
      obtain ⟨C'', hdd'', hfit'', hmin'', he''⟩ := ih _ hlt C' hdd' hB' rfl Z e''
      exact ⟨C'', hdd'', fun p k => (hfit'' p k).trans (hfit p k), hmin'', he''⟩

/-- **The Fitting ideals of two homotopy equivalent bounded-above complexes of finite free
modules over a local ring agree**, in every degree and at every index.

This is the proof of [Stacks, Tag 0ESP] over a local ring: split trivial two-term complexes off
both complexes until they are minimal above `p - 1`, which changes neither their Fitting ideals
nor the relation between them, and then compare the minimal complexes by Nakayama's lemma. -/
theorem fittingIdeal_eq_of_matrixHtpy {C₁ C₂ : FreeData R}
    (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0) (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (e : MatrixHtpy C₁ C₂) (p k : ℤ) : C₁.fittingIdeal p k = C₂.fittingIdeal p k := by
  obtain ⟨D₁, hddD₁, hfit₁, hmin₁, ⟨e₁⟩⟩ :=
    exists_minimal_above (p - 1) (max C₁.top C₂.top) _ C₁ hdd₁
      (fun j hj => C₁.rank_eq_zero_of_top_lt j (by omega)) rfl C₂ e
  obtain ⟨D₂, hddD₂, hfit₂, hmin₂, ⟨e₂⟩⟩ :=
    exists_minimal_above (p - 1) (max C₁.top C₂.top) _ C₂ hdd₂
      (fun j hj => C₂.rank_eq_zero_of_top_lt j (by omega)) rfl D₁ e₁.symm
  rw [← hfit₁ p k, ← hfit₂ p k]
  exact (fittingIdeal_eq_of_matrixHtpy_of_minimal e₂ (p - 1) hmin₂ hmin₁ p k (by omega)).symm

/-- **The Fitting ideals of two bounded-above complexes of finite free modules over a local ring
which are isomorphic in the derived category agree**, in every degree and at every index. This is
the model independence that the local description of [Stacks, Tag 0ESP] asserts, over a local
ring. -/
theorem fittingIdeal_eq_of_derivedIso [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {C₁ C₂ : FreeData R} (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0)
    (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (e : DerivedCategory.Q.obj (C₁.toCochain hdd₁) ≅ DerivedCategory.Q.obj (C₂.toCochain hdd₂))
    (p k : ℤ) : C₁.fittingIdeal p k = C₂.fittingIdeal p k := by
  let := C₁.isKProjective_toCochain hdd₁
  let := C₂.isKProjective_toCochain hdd₂
  obtain ⟨π, hπ⟩ := CochainComplex.exists_quasiIso_of_derived_iso
    (C₁.toCochain hdd₁) (C₂.toCochain hdd₂) C₁.top e
  obtain ⟨eq, -⟩ := (CochainComplex.IsKProjective.quasiIso_iff π).1 hπ
  exact fittingIdeal_eq_of_matrixHtpy hdd₁ hdd₂ (MatrixHtpy.ofHomotopyEquiv eq) p k

end Stacks.FittingComplex.FreeData

end
