module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# When the inverse image of a subspace maps isomorphically onto it

For a subfunctor `W` of `G` and a morphism `p : F ⟶ G`, the projection
`W.fromPreimage p : p⁻¹W ⟶ W` is an isomorphism as soon as *some* fibre product of `W.ι` along
`p` has its first projection invertible. This is the criterion needed when `p` itself is neither
a monomorphism nor an isomorphism, but becomes one after restricting over `W`.

The two criteria already available do not cover that case:

* `AlgebraicGeometry.Space.isIso_fromPreimage_of_le_range` requires `p` to be a monomorphism;
* the isomorphism case requires `p` itself to be invertible.

The motivating situation is Stacks 0AEV, where `f : Y ⟶ X` is flat and an isomorphism *over*
the closed subspace `Z` — so `Z.fromPreimage f` is invertible while `f` is neither a
monomorphism nor an isomorphism. For `X = Spec R` and `Y = Spec S` with `Z` cut out by an ideal
`I`, the hypothesis below is supplied by the base change of the closed immersion
`Spec (R ⧸ I) ⟶ Spec R` along `f`, whose first projection is `Spec` of the isomorphism
`R ⧸ I ≅ S ⧸ IS`.

## Main results

* `CategoryTheory.Subfunctor.isIso_fromPreimage_of_isIso_of_isPullback`: if a fibre product of
  `W.ι` along `p` has invertible first projection, then `W.fromPreimage p` is invertible.

## Implementation notes

The proof is the uniqueness of a fibre product. `CategoryTheory.Subfunctor.fromPreimage` is
itself a first projection of a fibre product of the same cospan, by
`CategoryTheory.Subfunctor.isPullback_fromPreimage`, so the comparison
`CategoryTheory.IsPullback.isoIsPullback` of the two is an isomorphism commuting with the two
first projections; the given projection being invertible then makes `W.fromPreimage p` a
composite of two isomorphisms.

The hypothesis is stated as an `IsPullback` on an arbitrary object rather than on
`CategoryTheory.Limits.pullback`, so that a square already proved cartesian elsewhere can be
passed without first comparing it to the chosen pullback.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Subfunctor

/-- **The inverse image of a subfunctor maps isomorphically onto it when some fibre product of
its inclusion has invertible first projection.**

Unlike `AlgebraicGeometry.Space.isIso_fromPreimage_of_le_range` this asks nothing of `p` itself:
`p` may be neither a monomorphism nor an isomorphism, as long as it becomes an isomorphism after
base change to `W`. -/
theorem isIso_fromPreimage_of_isIso_of_isPullback {C : Type u} [Category.{v} C]
    {F G H : C ⥤ Type v} (W : Subfunctor G) (p : F ⟶ G)
    {q : H ⟶ W.toFunctor} {g : H ⟶ F} (hsq : IsPullback q g W.ι p) [IsIso q] :
    IsIso (W.fromPreimage p) := by
  have hpre := W.isPullback_fromPreimage p
  have hhom : (hsq.isoIsPullback _ _ hpre).hom ≫ W.fromPreimage p = q := by simp
  have heq : W.fromPreimage p = (hsq.isoIsPullback _ _ hpre).inv ≫ q :=
    (Iso.eq_inv_comp _).2 hhom
  rw [heq]
  infer_instance

end CategoryTheory.Subfunctor

end
