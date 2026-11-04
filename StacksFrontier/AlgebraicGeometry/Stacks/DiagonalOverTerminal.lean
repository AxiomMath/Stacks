module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalCriteria

/-!
# The absolute diagonal as a relative diagonal (Stacks 07WG, Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B`. The 2-category of categories fibred in
groupoids over the big fppf site of `S` has a final object, the site itself with the identity as
structure functor, and the product `𝒳 × 𝒳` is by definition the 2-fibre product of `𝒳` with
itself over that final object. Consequently the *absolute* diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is the
*relative* diagonal of the structure 1-morphism `𝒳 ⟶ *`, on the nose.

The point of recording this is that the relative diagonal criterion
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff` (Stacks 04XT)
then applies to the absolute diagonal, and so describes condition (1) of Stacks 045G presheaf by
presheaf *without* chosen pullbacks: it is equivalent to saying that for every scheme `U` over
`S` and every point `Y` of `𝒳 ×_𝒞 𝒳` over the big fppf site of `U` the presheaf of vertical
morphisms between the two components of `Y` is an algebraic space over `U`. This is the form in
which condition (2) of Stacks 07WG — which asks for condition (1) of Stacks 045G for each
`𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳} 𝒱` — is usable, because the objects of such a `𝒴` are explicit quadruples
and its morphisms are described by
`CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.exists_hom_b_eq_iff`, while the chosen
pullbacks of a 2-fibre product are not explicit at all.

## Main definitions

* `AlgebraicGeometry.Stack.terminalCFG`: the final object of the 2-category of categories fibred
  in groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.toTerminalCFG`: the structure 1-morphism of `𝒳` to it.

## Main results

* `AlgebraicGeometry.Stack.diagonalBasedFunctor_eq_relativeDiagonalBasedFunctor`: the absolute
  diagonal is the relative diagonal of the structure 1-morphism to the final object.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonal_iff`: Stacks 04XT applied to
  the absolute diagonal, which is the presheaf form of condition (1) of Stacks 045G.

## Implementation notes

The identification is an equality of 1-morphisms, not merely an equivalence: the product
`CategoryTheory.CatFiberedInGroupoids.product` is built from
`CategoryTheory.TwoFibreProductOver.structureFunctor` with middle leg `𝟭 𝒞` and both outer legs
the structure functor of `𝒳`, which is literally `AlgebraicGeometry.Stack.twoFibreProduct` taken
at `terminalCFG` and at the structure 1-morphism; and the witness that the diagonal is a
1-morphism over the site is `CategoryTheory.Functor.comp_id` on both sides. The remaining field
of a `CategoryTheory.CatFiberedInGroupoids` is a proof, so proof irrelevance closes the gap
between the two ways of producing it.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The final object of the 2-category of categories fibred in groupoids over the big fppf site
of `S`: the site itself, with the identity functor as structure functor. -/
def terminalCFG : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
    Functor.isFiberedInGroupoids_id

/-- The structure 1-morphism of a category fibred in groupoids to the final object: its structure
functor, which is a 1-morphism over the site because composing with the identity changes
nothing. -/
def toTerminalCFG (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    𝒳.val ⥤ᵇ (terminalCFG B S hS).val where
  toFunctor := 𝒳.val.p
  w := Functor.comp_id _

/-- **The absolute diagonal is the relative diagonal of the structure 1-morphism to the final
object.** -/
lemma diagonalBasedFunctor_eq_relativeDiagonalBasedFunctor
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    diagonalBasedFunctor B S hS 𝒳
      = relativeDiagonalBasedFunctor B S hS 𝒳 (terminalCFG B S hS) (toTerminalCFG B S hS 𝒳) :=
  rfl

/-- **Condition (1) of Stacks 045G, presheaf by presheaf.** The diagonal of a category fibred in
groupoids over the big fppf site of `S` is representable by algebraic spaces if and only if, for
every scheme `U` over `S` and every point `Y` of `𝒳 ×_𝒞 𝒳` over the big fppf site of `U`, the
presheaf of vertical morphisms between the two components of `Y` is an algebraic space over `U`.
This is Stacks 04XT (`isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`) applied to the
structure 1-morphism to the final object. -/
theorem isRepresentableByAlgebraicSpaces_diagonal_iff
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳) ↔
      ∀ (U : BigFppfOver B S hS)
        (Y : BigFppfOver B U.left.1 U.left.2 ⥤
          TwoFibreProductOver 𝒳.val.p 𝒳.val.p (terminalCFG B S hS).val.p
            (toTerminalCFG B S hS 𝒳).toFunctor (toTerminalCFG B S hS 𝒳).toFunctor)
        (hY : Y ⋙ RelProdP 𝒳.val.p (terminalCFG B S hS).val.p
            (toTerminalCFG B S hS 𝒳).toFunctor = Over.map U.hom),
        ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
          IsAlgebraicSpace B U.left.1 U.left.2 F ∧
            Nonempty (relVertHomPresheaf (terminalCFG B S hS).isFiberedInGroupoids
                𝒳.isFiberedInGroupoids hY (toTerminalCFG B S hS 𝒳).w ⋙
                uliftFunctor.{u, v} ≅ F ⋙ uliftFunctor.{v, u}) :=
  isRepresentableByAlgebraicSpaces_relativeDiagonal_iff B S hS 𝒳 (terminalCFG B S hS)
    (toTerminalCFG B S hS 𝒳)

end AlgebraicGeometry.Stack

end
