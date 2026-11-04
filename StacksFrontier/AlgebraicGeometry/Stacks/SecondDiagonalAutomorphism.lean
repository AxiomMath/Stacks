module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.CategoryTheory.FiberedCategory.SubsingletonPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SecondDiagonalFibre

/-!
# Condition (1) of Stacks 07WG: the locus where an automorphism is trivial

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. The proof of Stacks 07WG reads its condition (1) —
representability by algebraic spaces of the second diagonal

`Δ_Δ : 𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`

— as the following statement:

> Given a scheme `V`, an object `x` of `𝒳` over `V` and a morphism `α : x ⟶ x` of `𝒳_V`, the
> condition "`α = 𝟙 x`" defines an algebraic space over `V`. In other words, there is a
> monomorphism of algebraic spaces `W → V` such that a morphism of schemes `f : T → V` factors
> through `W` if and only if `f^*α = 𝟙 (f^*x)`.

This file proves that reading, with the quantification over `(V, x, α)` replaced by the one that
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` itself uses: over objects `U` of the
site and 1-morphisms `Y` from the big fppf site of `U` into the second 2-fibre product
`𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` over the site. The automorphism attached to such a `Y` at an object `a`
is `CategoryTheory.TwoFibreProductOver.diagonalAut`, the composite `φ₁ ∘ φ₂⁻¹` of the two
components of the comparison isomorphism of `Y a`; under the identification of the second
2-fibre product with the inertia of `𝒳` it is the automorphism component of `Y a`.

"Defines an algebraic space" is rendered as: there is an algebraic space `F` over `U` which is a
*subobject of the final presheaf* — all of its values are subsingletons, which is exactly the
monomorphism `W → V` of the source's parenthesis — and which is nonempty over `a` precisely when
the automorphism attached to `Y a` is the identity. A presheaf of subsingletons carries no
information beyond its support, so these two clauses pin `F` up to isomorphism; that is
`CategoryTheory.presheafIsoOfSubsingleton`, and it is what makes this reading equivalent to
representability rather than merely implied by it.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_secondDiagonal_iff_automorphism`:
  condition (1) of **Stacks 07WG** in the form displayed above.

## Implementation notes

Both directions go through Stacks 04XT
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`), which
describes representability of a relative diagonal by the presheaf of vertical morphisms lying
over the comparison isomorphism of a point of the target, and through the evaluation of that
presheaf at the second diagonal: it has at most one section over each object
(`CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.subsingleton_relVertHom`) and it has one
exactly when the automorphism is the identity
(`CategoryTheory.TwoFibreProductOver.SecondDiagonalFibre.nonempty_relVertHom_iff`). So the
statement is obtained from 04XT by replacing the comparison isomorphism of presheaves with the
pair of conditions that determines it, in the forward direction by transporting them along the
given isomorphism and in the backward direction by building the isomorphism from them.

No chosen pullbacks are needed, because the absolute diagonal of `𝒳` is the relative diagonal of
the structure 1-morphism to the final object
(`AlgebraicGeometry.Stack.diagonalBasedFunctor_eq_relativeDiagonalBasedFunctor`) and 04XT applies
to the relative diagonal of any 1-morphism. The universes of `𝒳` stay independent: the presheaf
of vertical morphisms takes values in the morphism universe of `𝒳` while the representing
algebraic space takes values in the universe of the site, and the two are compared after the
universe lifts that Stacks 02ZW performs.

The statement is untagged. Tag 07WG is the equivalence of its two conditions, which is not
proved here; this is the first of the two conditions, in the form its proof uses.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.TwoFibreProductOver
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (1) of Stacks 07WG.** The second diagonal of a category fibred in groupoids over
the big fppf site of `S` is representable by algebraic spaces if and only if, for every object
`U` of the site and every 1-morphism `Y` from the big fppf site of `U` into the second 2-fibre
product `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` over the site, the condition that the automorphism attached to
`Y a` be the identity defines an algebraic space over `U` — a subobject of the final presheaf,
i.e. a monomorphism of algebraic spaces, whose support is exactly that condition.

This is the sentence the proof of Stacks 07WG opens with: for a scheme `V`, an object `x` of `𝒳`
over `V` and a morphism `α : x ⟶ x` of `𝒳_V`, the condition "`α = 𝟙 x`" defines an algebraic
space over `V`. -/
theorem isRepresentableByAlgebraicSpaces_secondDiagonal_iff_automorphism
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
          (diagonalBasedFunctor B S hS 𝒳)) ↔
      ∀ (U : BigFppfOver B S hS)
        (Y : BigFppfOver B U.left.1 U.left.2 ⥤
          TwoFibreProductOver 𝒳.val.p 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
            (diagonalBasedFunctor B S hS 𝒳).toFunctor (diagonalBasedFunctor B S hS 𝒳).toFunctor)
        (_hY : Y ⋙ RelProdP 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
            (diagonalBasedFunctor B S hS 𝒳).toFunctor = Over.map U.hom),
        ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
          IsAlgebraicSpace B U.left.1 U.left.2 F ∧
            (∀ a, Subsingleton (F.obj a)) ∧
            ∀ a, Nonempty (F.obj (op a)) ↔
              (diagonalAut (Functor.comp_id 𝒳.val.p) (Y.obj a)).hom = 𝟙 (Y.obj a).x := by
  rw [isRepresentableByAlgebraicSpaces_relativeDiagonal_iff B S hS 𝒳
    (CatFiberedInGroupoids.product 𝒳 𝒳) (diagonalBasedFunctor B S hS 𝒳)]
  constructor
  · intro h U Y hY
    obtain ⟨F, hF, ⟨e⟩⟩ := h U Y hY
    exact ⟨F, hF,
      subsingleton_of_iso_comp_uliftFunctor e
        (fun a => SecondDiagonalFibre.subsingleton_relVertHom
          (Functor.comp_id 𝒳.val.p) Y a.unop),
      fun a => (nonempty_iff_of_iso_comp_uliftFunctor e (op a)).symm.trans
        (SecondDiagonalFibre.nonempty_relVertHom_iff (Functor.comp_id 𝒳.val.p) Y a hY)⟩
  · intro h U Y hY
    obtain ⟨F, hF, hFsub, hFsupp⟩ := h U Y hY
    exact ⟨F, hF, nonempty_iso_comp_uliftFunctor_of_subsingleton
      (fun a => SecondDiagonalFibre.subsingleton_relVertHom
        (Functor.comp_id 𝒳.val.p) Y a.unop) hFsub
      (fun a => (SecondDiagonalFibre.nonempty_relVertHom_iff
        (Functor.comp_id 𝒳.val.p) Y a.unop hY).trans (hFsupp a.unop).symm)⟩

end AlgebraicGeometry.Stack

end
