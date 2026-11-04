module

public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism

/-!
# Being a derived limit transfers across a pro-isomorphism of towers

Let `D` be a pre-triangulated category and let `F, G : ℕᵒᵖ ⥤ D` be inverse systems which are
isomorphic as pro-objects, `InverseSequence.ProIso F G`. This file records that an object which
is a derived limit of `F` is a derived limit of `G`.

[Stacks, Tag 0H9L], `Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism`, compares a
derived limit of `F` with a *given* derived limit of `G` and produces a non-canonical
isomorphism between them. The statement here is the same fact read as a transfer of the
predicate rather than as a comparison of two objects: a derived limit `K'` of `G` exists as soon
as the product of its terms does, 0H9L identifies it with the given `K`, and being a derived
limit of a fixed system is invariant under isomorphism of the limit object
(`CategoryTheory.Pretriangulated.IsDerivedLimit.of_isoObj`).

That reading is what a statement of the form "`K^∧ = R lim Lₙ`" needs: `R lim` is a predicate
rather than a functor in this development, so such a statement is `IsDerivedLimit L K^∧`, and
proving it from a presentation of `K^∧` as a derived limit of a pro-isomorphic tower is exactly
this lemma. Nothing about the isomorphism 0H9L produces is used, so no canonicity is lost — there
is no comparison map in the conclusion to be canonical about.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.of_proIso`: being a derived limit transfers
  across a pro-isomorphism of towers.

## References

* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Being a derived limit transfers across a pro-isomorphism of towers.** If the inverse
systems `F, G : ℕᵒᵖ ⥤ D` are isomorphic as pro-objects and `K` is a derived limit of `F`, then
`K` is a derived limit of `G`.

A derived limit `K'` of `G` exists because the product of its terms does
(`CategoryTheory.Pretriangulated.exists_isDerivedLimit`), [Stacks, Tag 0H9L] gives an
isomorphism `K ≅ K'`, and `CategoryTheory.Pretriangulated.IsDerivedLimit.of_isoObj` carries the
property back along it. -/
theorem IsDerivedLimit.of_proIso {F G : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (a : InverseSequence.ProIso F G) {K : D} (hK : IsDerivedLimit F K) :
    IsDerivedLimit G K := by
  obtain ⟨K', hK'⟩ := exists_isDerivedLimit G
  obtain ⟨e⟩ :=
    _root_.Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism F G K K' hK hK' a
  exact IsDerivedLimit.of_isoObj e.symm hK'

end CategoryTheory.Pretriangulated

end
