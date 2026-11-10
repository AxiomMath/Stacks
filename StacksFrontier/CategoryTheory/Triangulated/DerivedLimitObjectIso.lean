module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Being a derived limit transports along an isomorphism of the limit object

Let `D` be a pre-triangulated category, `F : ℕᵒᵖ ⥤ D` an inverse system whose objects have a
product, and `L` a derived limit of `F` in the sense of
`CategoryTheory.Pretriangulated.IsDerivedLimit`. Any object isomorphic to `L` is then a derived
limit of `F` as well.

This completes the transport API of that predicate: `IsDerivedLimit.of_iso` and
`IsDerivedLimit.of_natIso` move a derived limit along an isomorphism of the *system*, and this
file moves it along an isomorphism of the *object*. Both are needed because a derived limit is
determined only up to non-unique isomorphism, so a formula for `R lim Fₙ` produced by one
construction has to be carried to the object another construction names.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.of_objIso`: if `K ≅ L` and `L` is a derived
  limit of `F`, then so is `K`.

## Implementation notes

The module
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientKoszulLimit`
carries a `private` copy of this statement, written before it was available anywhere; this is
the public form, and new consumers should use it.

## References

* [Stacks, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Being a derived limit transports along an isomorphism of the limit object.** If `K ≅ L`
and `L = R lim Fₙ`, then `K = R lim Fₙ`.

The triangle `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L⟦1⟧` witnessing the hypothesis is isomorphic, through the
given isomorphism in the first slot and the identity in the other two, to one of the same shape
with `K` in the first slot; the middle map is the difference map in both, so the second triangle
witnesses the conclusion. -/
theorem IsDerivedLimit.of_objIso {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K L : D}
    (e : K ≅ L) (hL : IsDerivedLimit F L) : IsDerivedLimit F K := by
  obtain ⟨p, δ, hT⟩ := hL
  refine ⟨e.hom ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.inv,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simp
  · simp
  · simp

end CategoryTheory.Pretriangulated

end
