module

public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison

/-!
# Vanishing of sheaf cohomology above a bound read off a finite cover

Let `G` be an abelian sheaf on a topological space and let `U i`, `i ∈ J`, be a finite family of
opens. Suppose a function `τ` on finite index sets bounds the vanishing range of `G` over the
intersections: `H^p(⋂_{i ∈ s} U i, G) = 0` for `p ≥ τ s`. Then the cohomology of `G` over
`⋃_{i ∈ J} U i` vanishes in degrees at least `|s| + τ s - 1` for every nonempty `s ⊆ J`.

This single induction is the combinatorial content of both [Stacks, Tag 01XI] — where the `U i`
are affine, so `τ ≡ 1` works and the bound is the number of pieces — and [Stacks, Tag 071L],
where the `U i` are quasi-compact with affine diagonal and `τ s` is the affine covering number
of the intersection.

## Main results

* `Stacks.Cohomology.UniformVanishing.isZero_sheafCohomology_finsetSup`: the induction, in the
  form that takes any `d` dominating all the numbers `|s| + τ s - 1`.

## Implementation notes

The induction is on the index set `J`, adding one open `U a` at a time, and the inductive step
is the Mayer--Vietoris vanishing step `isZero_sheafCohomology_sup`. Running it over a `Finset`
rather than over `Fin n` is what lets the two recursive calls — one for the union of the
remaining opens, one for its intersection with `U a` — reuse the same statement: the second call
is the same statement for the family `i ↦ U i ⊓ U a` with `τ` shifted by inserting `a`, and the
intersections of that family are intersections of the original one. The step where only one open
is left is handled separately rather than through the Mayer--Vietoris sequence, because the bound
may be `0` there and the Mayer--Vietoris step needs a positive degree.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Cohomology.UniformVanishing

variable {T : Type u} [TopologicalSpace T]
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]

/-- Over a nonempty finite index set, intersecting every member of a family with a fixed element
is the same as intersecting the whole intersection with it. -/
theorem finsetInf_inf {α : Type*} [Lattice α] [OrderTop α] {ι : Type*} (f : ι → α) (a : α)
    {s : Finset ι} (hs : s.Nonempty) : s.inf (fun i ↦ f i ⊓ a) = s.inf f ⊓ a := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
      rw [Finset.inf_cons, Finset.inf_cons, ih, inf_assoc, inf_assoc, inf_left_comm a, inf_idem]

/-- **Vanishing above a bound read off a finite cover.** Let `G` be an abelian sheaf on a space,
`U` a family of opens and `τ` a function on finite index sets such that the cohomology of `G`
over `⋂_{i ∈ s} U i` vanishes in degrees at least `τ s`, for every nonempty `s`. If `d` is at
least `|s| + τ s - 1` for every nonempty `s ⊆ J`, then the cohomology of `G` over
`⋃_{i ∈ J} U i` vanishes in degrees at least `d`. -/
theorem isZero_sheafCohomology_finsetSup
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) {ι : Type*}
    (J : Finset ι) :
    ∀ (U : ι → Opens T) (τ : Finset ι → ℕ) (d : ℕ),
      (∀ s : Finset ι, s.Nonempty → ∀ p : ℕ, τ s ≤ p → IsZero (Sheaf.H' G p (s.inf U))) →
      (∀ s ⊆ J, s.Nonempty → s.card + τ s - 1 ≤ d) →
      ∀ p : ℕ, d ≤ p → IsZero (Sheaf.H' G p (J.sup U)) := by
  classical
  induction J using Finset.induction with
  | empty =>
      intro U τ d _ _ p _
      simpa using isZero_sheafCohomology_bot G p
  | @insert a J ha ih =>
      intro U τ d hτ hJ p hp
      have hsingleton : τ {a} ≤ p := by
        have h := hJ {a} (by simp) ⟨a, by simp⟩
        simp only [Finset.card_singleton] at h
        omega
      have hR : IsZero (Sheaf.H' G p (U a)) := by
        simpa using hτ {a} ⟨a, by simp⟩ p hsingleton
      have hsup : (insert a J).sup U = J.sup U ⊔ U a := by
        rw [Finset.sup_insert]; exact sup_comm _ _
      rcases J.eq_empty_or_nonempty with rfl | hJne
      · simpa [hsup] using hR
      obtain ⟨b, hb⟩ := hJne
      have hab : a ≠ b := fun h ↦ ha (h ▸ hb)
      have hd1 : 1 ≤ d := by
        have h := hJ {a, b} (by
          refine Finset.insert_subset_insert a ?_
          simpa using hb) ⟨a, by simp⟩
        rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at h
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have hL : IsZero (Sheaf.H' G (q + 1) (J.sup U)) :=
        ih U τ d hτ (fun s hs hsne ↦ hJ s (hs.trans (Finset.subset_insert a J)) hsne) (q + 1) hp
      have hLR : IsZero (Sheaf.H' G q (J.sup U ⊓ U a)) := by
        rw [Finset.sup_inf_distrib_right]
        refine ih (fun i ↦ U i ⊓ U a) (fun s ↦ τ (insert a s)) (d - 1) ?_ ?_ q (by omega)
        · intro s hsne pp hpp
          have hinf : s.inf (fun i ↦ U i ⊓ U a) = (insert a s).inf U := by
            rw [finsetInf_inf U (U a) hsne, Finset.inf_insert, inf_comm]
          rw [hinf]
          exact hτ (insert a s) ⟨a, by simp⟩ pp hpp
        · intro s hs hsne
          have hmem : a ∉ s := fun h ↦ ha (hs h)
          have h := hJ (insert a s) (Finset.insert_subset_insert a hs) ⟨a, by simp⟩
          rw [Finset.card_insert_of_notMem hmem] at h
          omega
      rw [hsup]
      exact isZero_sheafCohomology_sup G (J.sup U) (U a) q hL hR hLR

end Stacks.Cohomology.UniformVanishing
