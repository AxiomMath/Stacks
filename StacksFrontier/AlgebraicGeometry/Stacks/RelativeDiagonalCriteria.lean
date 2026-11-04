module

public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre

/-!
# The relative diagonal criterion (Stacks 04XT)

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` and `𝒴` be categories fibred in
groupoids over the big fppf site of `S` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism over the site. Its
relative diagonal is

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`.

This file characterizes representability of `Δ_f` by algebraic spaces (Stacks 02ZW) presheaf by
presheaf: `Δ_f` is representable by algebraic spaces exactly when, for every scheme `U` over `S`
and every point `Y` of `𝒳 ×_𝒴 𝒳` over the big fppf site of `U`, the presheaf of *vertical
morphisms over the comparison isomorphism of `Y`* is an algebraic space over `U`. That presheaf
sends an object `a` of the site of `U` to the set of vertical morphisms `m : Y₁ a ⟶ Y₂ a` of `𝒳`
with `f m = α a`, where `Y₁`, `Y₂` are the two components of `Y` and `α` is its comparison
isomorphism; in sheaf-theoretic terms it is the fibre product

`Isom_𝒳(Y₁, Y₂) ×_{Isom_𝒴(f Y₁, f Y₂), α} U`,

which is the cartesian square labelled 04XT in the proof of Stacks 04XS.

This is the relative counterpart of the first equivalence of Stacks 045G
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`), and like
it, no result about algebraic spaces enters: the same presheaf works on both sides, and all that
happens is that an equivalence over the site of `U` with the category of elements of a presheaf
is traded for an isomorphism of universe-lifted presheaves. The two inputs are
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver`, which identifies the
2-fibre product of `Y` with `Δ_f` with the category of elements of that presheaf, and
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_iff`, which says that the category
of elements determines the presheaf.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`: **Stacks
  04XT**, the relative diagonal criterion.

## Implementation notes

The condition is stated by quantifying over 1-morphisms `Y` from the big fppf site of `U` into
`𝒳 ×_𝒴 𝒳` over the site, rather than over triples `(x, x', α)` in the fibre over `U`: that is
the shape `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` quantifies in, so the two
sides of the equivalence match clause by clause and the only content is the comparison of the
inner existentials. Translating the quantifier into one over fibre objects is the 2-Yoneda step
that `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`
performs for the absolute diagonal; it is not done here, because the consumer of this
criterion — condition (1) of Stacks 07WG, where `f` is itself the diagonal of `𝒳` — needs the
1-morphism form.

The universes of `𝒳` and `𝒴` are independent, as the predicate of Stacks 02ZW allows, and the
presheaf of vertical morphisms takes values in the morphism universe of `𝒳`. The statement is
untagged: 04XT is the square inside the proof of Stacks 04XS, whose own statement is about
algebraic stacks and is not available here.

## References

* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (𝒴 : CatFiberedInGroupoids.{u, v', u + 1, w'} (BigFppfOver B S hS))
  (f : 𝒳.val ⥤ᵇ 𝒴.val)

/-- **Stacks 04XT, the relative diagonal criterion.** The relative diagonal of a 1-morphism `f`
of categories fibred in groupoids over the big fppf site of `S` is representable by algebraic
spaces if and only if, for every scheme `U` over `S` and every point `Y` of `𝒳 ×_𝒴 𝒳` over the
big fppf site of `U`, the presheaf of vertical morphisms between the two components of `Y` lying
over the comparison isomorphism of `Y` is an algebraic space over `U`. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_iff :
    IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f) ↔
      ∀ (U : BigFppfOver B S hS)
        (Y : BigFppfOver B U.left.1 U.left.2 ⥤
          TwoFibreProductOver 𝒳.val.p 𝒳.val.p 𝒴.val.p f.toFunctor f.toFunctor)
        (hY : Y ⋙ RelProdP 𝒳.val.p 𝒴.val.p f.toFunctor = Over.map U.hom),
        ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
          IsAlgebraicSpace B U.left.1 U.left.2 F ∧
            Nonempty (relVertHomPresheaf 𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hY f.w ⋙
                uliftFunctor.{u, v} ≅ F ⋙ uliftFunctor.{v, u}) := by
  dsimp only [IsRepresentableByAlgebraicSpaces]
  exact forall_congr' fun U => forall_congr' fun Y => forall_congr' fun hY =>
    exists_congr fun F => and_congr_right' <|
      nonempty_equivalenceOver_fst_iff 𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hY f.w F

end AlgebraicGeometry.Stack

end
