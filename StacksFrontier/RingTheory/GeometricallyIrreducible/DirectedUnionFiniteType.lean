module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra

/-!
# A geometrically irreducible algebra is the directed union of finite type ones

Let `k` be a field and `S` a geometrically irreducible `k`-algebra, for instance a geometrically
irreducible field extension `K/k`. Then `S` is the directed union of its finitely generated
`k`-subalgebras, and each of them is again geometrically irreducible over `k` (Stacks 037N, part
(1)). This is the first sentence of the argument of Stacks Remark 0BA7: `K` is the limit of
geometrically irreducible finite type `k`-algebras.

## Main results

* `Algebra.IsGeometricallyIrreducible.exists_directed_fg_subalgebras`: the finitely generated
  subalgebras of a geometrically irreducible `k`-algebra form a directed family of geometrically
  irreducible finite type `k`-algebras whose union is everything.

## References

* [Stacks Project, Tag 037N](https://stacks.math.columbia.edu/tag/037N)
* [Stacks Project, Tag 0BA7](https://stacks.math.columbia.edu/tag/0BA7)
-/

@[expose] public section

universe u

namespace Algebra.IsGeometricallyIrreducible

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- **A geometrically irreducible algebra is the directed union of geometrically irreducible
finite type subalgebras.** The finitely generated `k`-subalgebras of a geometrically irreducible
`k`-algebra `S` form a directed family whose supremum is `S`; each member is of finite type over
`k` and geometrically irreducible over `k`. -/
theorem exists_directed_fg_subalgebras (hS : Algebra.IsGeometricallyIrreducible k S) :
    ∃ (ι : Type u) (A : ι → Subalgebra k S), Directed (· ≤ ·) A ∧ (⨆ i, A i) = ⊤ ∧
      ∀ i, Algebra.FiniteType k (A i) ∧ Algebra.IsGeometricallyIrreducible k (A i) := by
  refine ⟨{A : Subalgebra k S // A.FG}, fun A => A.1, ?_, ?_, fun A => ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨⟨A ⊔ B, hA.sup hB⟩, le_sup_left, le_sup_right⟩
  · refine Algebra.eq_top_iff.mpr fun x => ?_
    have hfg : (Algebra.adjoin k {x}).FG := ⟨{x}, by simp⟩
    exact (le_iSup (fun A : {A : Subalgebra k S // A.FG} => A.1) ⟨_, hfg⟩)
      (Algebra.self_mem_adjoin_singleton k x)
  · exact (Subalgebra.fg_iff_finiteType A.1).mp A.2
  · exact isGeometricallyIrreducible_of_subalgebra k S hS A.1

end Algebra.IsGeometricallyIrreducible
