module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackDiagonalMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibres

/-!
# The fibre of the diagonal is the diagonal of the fibres

Let `G : 𝒮 ⥤ 𝒮'` be a functor strictly over a base category `𝒞`, and let
`Δ_G : 𝒮 ⥤ 𝒮 ×_{G, 𝒮', G} 𝒮` be its diagonal
(`CategoryTheory.TwoFibreProductOver.diagonal`). Stacks 02XI identifies the fibre of the
2-fibre product over an object `U` of `𝒞` with the 2-fibre product of the fibres
(`CategoryTheory.TwoFibreProductOver.toFiberPullback`), and under that identification the functor
induced by `Δ_G` on the fibres over `U` is the diagonal of the functor `G_U` induced by `G`. Both
send an object `x` of `𝒮_U` to the triple `(x, x, 𝟙)` and a morphism `φ` to the pair `(φ, φ)`, so
the identification is an equality of functors and not merely an isomorphism.

The same statement is then transported across the universe lift `CategoryTheory.AsSmall.up`,
which is where it is used: the squares of Stacks 0CMR are squares of `Cat` at a single pair of
universes, so every fibre appearing in one of them has been lifted.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.asSmallFiberPullback`: the comparison of Stacks 02XI
  followed by the universe lift of its target, that is, the comparison
  `AsSmall (𝒳 ×_𝒮 𝒴)_U ⥤ AsSmall 𝒳_U ×_{AsSmall 𝒮_U} AsSmall 𝒴_U`.

## Main results

* `CategoryTheory.TwoFibreProductOver.fiberFunctor_diagonal_comp_toFiberPullback`: the fibre of
  the diagonal is the diagonal of the fibre.
* `CategoryTheory.Limits.CategoricalPullback.diagonal_comp_asSmallMap`: the universe lift of a
  diagonal is the diagonal of the universe lift, a case of
  `CategoryTheory.Limits.CategoricalPullback.diagonal_comp_map`.
* `CategoryTheory.TwoFibreProductOver.fiberFunctor_diagonal_comp_asSmallFiberPullback`: the two
  previous results combined, which is the form the square of Stacks 0CMR needs.

## Implementation notes

That the diagonal is strictly over `𝒞`, which the induced functor on fibres needs, is the
pre-existing `CategoryTheory.TwoFibreProductOver.diagonal_comp_structureFunctor` of
`StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal`.

The three total categories are taken at one and the same pair of universes. That is the shape in
which the statement is used -- the categories fibred in groupoids of a 2-fibre product over the
big fppf site all lie at the absorbing universe shape of
`AlgebraicGeometry.BigFppfOver.twoFibreProduct` -- and it is what lets the universe lift of the
whole cospan be written with one lift parameter.

## References

* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe t v₁ v₂ u₁ u₂

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Functor.Fiber Functor.Fiber.fiberInclusion

namespace Limits.CategoricalPullback

variable {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]

/-- **The universe lift of a diagonal is the diagonal of the universe lift.** Both send an
object `x` to the triple `(up x, up x, 𝟙)`. This is the case of
`CategoryTheory.Limits.CategoricalPullback.diagonal_comp_map` in which the strictly commuting
square is the one saying that the two universe lifts cancel. -/
lemma diagonal_comp_asSmallMap (H : X ⥤ Y) :
    diagonal H ⋙ CategoricalPullback.map H H AsSmall.up.{v₁, u₁, t} AsSmall.up.{v₁, u₁, t}
          AsSmall.up.{v₂, u₂, t}
          (AsSmall.down ⋙ H ⋙ AsSmall.up.{v₂, u₂, t})
          (AsSmall.down ⋙ H ⋙ AsSmall.up.{v₂, u₂, t})
          (eqToIso rfl) (eqToIso rfl) =
      AsSmall.up.{v₁, u₁, t} ⋙ diagonal (AsSmall.down ⋙ H ⋙ AsSmall.up.{v₂, u₂, t}) :=
  diagonal_comp_map H (AsSmall.down ⋙ H ⋙ AsSmall.up.{v₂, u₂, t})
    AsSmall.up.{v₁, u₁, t} AsSmall.up.{v₂, u₂, t} rfl

end Limits.CategoricalPullback

namespace TwoFibreProductOver

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₂} [Category.{v₂} 𝒴]
variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

section AsSmall

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- **Stacks 02XI after a universe lift.** The comparison of the fibre of a 2-fibre product with
the 2-fibre product of the fibres, followed by the universe lift of its target: this is the
comparison in the universes at which the squares of Stacks 0CMR are stated. -/
def asSmallFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    AsSmall.{t} ((structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) ⥤
      CategoricalPullback
        (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒳 p𝒮 F hF U ⋙
          AsSmall.up.{v₂, u₂, t})
        (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒴 p𝒮 G hG U ⋙
          AsSmall.up.{v₂, u₂, t}) :=
  AsSmall.down ⋙ toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
    CategoricalPullback.map (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)
      AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t}
      (AsSmall.down ⋙ Functor.fiberMap p𝒳 p𝒮 F hF U ⋙ AsSmall.up.{v₂, u₂, t})
      (AsSmall.down ⋙ Functor.fiberMap p𝒴 p𝒮 G hG U ⋙ AsSmall.up.{v₂, u₂, t})
      (eqToIso rfl) (eqToIso rfl)

/-- **The comparison of Stacks 02XI stays an equivalence after the universe lift**, both the lift
of the source and the lift of the target being equivalences -- the latter by Stacks 02XB (3) for
the lift of a cospan. -/
instance isEquivalence_asSmallFiberPullback (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞) :
    (asSmallFiberPullback.{t} p𝒳 p𝒴 p𝒮 F G hF hG U).IsEquivalence :=
  letI : (toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).IsEquivalence :=
    (fiberEquiv p𝒳 p𝒴 p𝒮 F G hF hG U).isEquivalence_functor
  inferInstanceAs ((AsSmall.down ⋙ toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
    CategoricalPullback.map (Functor.fiberMap p𝒳 p𝒮 F hF U) (Functor.fiberMap p𝒴 p𝒮 G hG U)
      AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t}
      (AsSmall.down ⋙ Functor.fiberMap p𝒳 p𝒮 F hF U ⋙ AsSmall.up.{v₂, u₂, t})
      (AsSmall.down ⋙ Functor.fiberMap p𝒴 p𝒮 G hG U ⋙ AsSmall.up.{v₂, u₂, t})
      (eqToIso rfl) (eqToIso rfl)).IsEquivalence)

end AsSmall

section Diagonal

variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒳}

/-- **The fibre of the diagonal is the diagonal of the fibre.** Composing the functor induced by
`Δ_G` on the fibres over `U` with the comparison of Stacks 02XI gives the diagonal of the functor
`G_U`: both send `x` to the triple `(x, x, 𝟙)` and a morphism `φ` to the pair `(φ, φ)`. -/
lemma fiberFunctor_diagonal_comp_toFiberPullback (hG : G ⋙ p𝒮' = p𝒮) (U : 𝒞) :
    Functor.fiberFunctorOfCompEq (diagonal_comp_structureFunctor hG) U ⋙
        toFiberPullback p𝒮 p𝒮 p𝒮' G G hG hG U =
      CategoricalPullback.diagonal (Functor.fiberMap p𝒮 p𝒮' G hG U) := rfl

/-- **The fibre of the diagonal is the diagonal of the fibre, after the universe lift.** This is
the form in which the identification enters the square of Stacks 0CMR, whose corners are all
universe lifts of fibres. -/
lemma fiberFunctor_diagonal_comp_asSmallFiberPullback (hG : G ⋙ p𝒮' = p𝒮) (U : 𝒞) :
    (AsSmall.down.{v₂, u₂, t} ⋙
          Functor.fiberFunctorOfCompEq (diagonal_comp_structureFunctor hG) U ⋙
          AsSmall.up) ⋙
        asSmallFiberPullback.{t} p𝒮 p𝒮 p𝒮' G G hG hG U =
      CategoricalPullback.diagonal
        (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒮 p𝒮' G hG U ⋙
          AsSmall.up.{v₂, u₂, t}) :=
  congrArg (fun H => AsSmall.down.{v₂, u₂, t} ⋙ H)
    ((congrArg
        (fun H => H ⋙ CategoricalPullback.map (Functor.fiberMap p𝒮 p𝒮' G hG U)
          (Functor.fiberMap p𝒮 p𝒮' G hG U)
          AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t} AsSmall.up.{v₂, u₂, t}
          (AsSmall.down ⋙ Functor.fiberMap p𝒮 p𝒮' G hG U ⋙ AsSmall.up.{v₂, u₂, t})
          (AsSmall.down ⋙ Functor.fiberMap p𝒮 p𝒮' G hG U ⋙ AsSmall.up.{v₂, u₂, t})
          (eqToIso rfl) (eqToIso rfl))
        (fiberFunctor_diagonal_comp_toFiberPullback hG U)).trans
      (CategoricalPullback.diagonal_comp_asSmallMap.{t} (Functor.fiberMap p𝒮 p𝒮' G hG U)))

end Diagonal

end TwoFibreProductOver

end CategoryTheory

end
