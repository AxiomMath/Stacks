module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackDiagonal

/-!
# The diagonal commutes with a change of cospan along a strictly commuting square

Let `H : A ⥤ C` and `H' : A' ⥤ C'` be functors and let `RX : A ⥤ A'`, `RY : C ⥤ C'` fit into a
*strictly* commuting square `RX ⋙ H' = H ⋙ RY`. The square induces a functor
`H ⊡ H ⥤ H' ⊡ H'` on the explicit 2-fibre products of Stacks 003R by the functoriality of
Stacks 02XA (`CategoryTheory.Limits.CategoricalPullback.map`, applied with the two transports of
the square as its 2-cells), and this file records that the induced functor carries the diagonal
of `H` to the diagonal of `H'`:

```
Δ_H ⋙ map … = RX ⋙ Δ_{H'}
```

Both sides send an object `x` of `A` to the triple `(RX x, RX x, 𝟙)`: the structural isomorphism
produced by `map` is `RY` applied to an identity, conjugated by the two transports of the square,
and those cancel because the two components of a diagonal coincide.

Every change of cospan appearing in the proof of Stacks 0CMW is of this shape -- the universe
lift of a cospan, the transition functor of a stagewise 2-fibre product, and the stagewise
comparison into the 2-fibre product of the colimits are all
`CategoryTheory.Limits.CategoricalPullback.map` along a strictly commuting square -- so this one
lemma serves all of them.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.diagonal_comp_map`: the statement above.

## Implementation notes

The lemma is stated over abstract categories rather than over objects of `Cat`, because the two
quiver instances a `Cat`-valued statement reaches -- `CategoryTheory.Cat.instQuiver` and the one
coming from the object's own `Category` field -- are not interchangeable at `implicit`
transparency, and the hypothesis `h₃` of
`CategoryTheory.Cat.categoricalPullback_obj_ext` then fails to typecheck. Over abstract
categories there is only one instance path.

## References

* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {C : Type u₂} {A' : Type u₃} {C' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} C] [Category.{v₃} A'] [Category.{v₄} C']

/-- **A change of cospan along a strictly commuting square carries the diagonal to the
diagonal.** Both sides send `x` to the triple `(RX x, RX x, 𝟙)`; the two transports the induced
functor inserts cancel because the two components of a diagonal coincide. -/
lemma diagonal_comp_map (H : A ⥤ C) (H' : A' ⥤ C') (RX : A ⥤ A') (RY : C ⥤ C')
    (hq : RX ⋙ H' = H ⋙ RY) :
    diagonal H ⋙ CategoricalPullback.map H H RX RX RY H' H' (eqToIso hq) (eqToIso hq.symm) =
      RX ⋙ diagonal H' := by
  refine CategoryTheory.Functor.ext
    (fun x => Cat.categoricalPullback_obj_ext (by simp) (by simp) ?_)
    (fun x y g => CategoricalPullback.Hom.ext ?_ ?_)
  · refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
    simp
  all_goals
    simp only [Functor.comp_map, CategoricalPullback.comp_fst, CategoricalPullback.comp_snd,
      CategoricalPullback.map_map_fst, CategoricalPullback.map_map_snd,
      Cat.categoricalPullback_eqToHom_fst, Cat.categoricalPullback_eqToHom_snd,
      diagonal_map_fst, diagonal_map_snd]
    exact Cat.eq_eqToHom_conj _ _ _ _ HEq.rfl

end CategoryTheory.Limits.CategoricalPullback

end
