module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverInduction
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorization

/-!
# Finite covers splitting a flat surjection Zariski locally (Stacks 0CQ6)

Let `Y` be a quasi-compact and quasi-separated algebraic space, `V ⊆ Y` a quasi-compact open
and `f : 𝒳 ⟶ V` a surjective, flat 1-morphism of algebraic stacks which is locally of finite
presentation. [Stacks, Tag 0CQ6] produces a finite surjective morphism `g : Y' ⟶ Y` such that
`g⁻¹(V) ⟶ V` factors Zariski locally through `f`.

`StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorization` proves this from the
existence of finite surjective scheme covers of quasi-compact quasi-separated algebraic spaces
(`Stack.exists_finite_surjective_zariskiLocal_factorization_of_finiteSchemeCover`);
that existence is the finite-surjective part of [Stacks, Proposition 09YC],
`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`.

## Main results

* `AlgebraicGeometry.Stack.exists_finite_surjective_zariskiLocal_factorization`:
  [Stacks, Tag 0CQ6] in full.

## References

* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **[Stacks, Tag 0CQ6].** Let `Y` be a quasi-compact and quasi-separated algebraic space over
`S`, let `V ⊆ Y` be a quasi-compact open subspace and let `f : 𝒳 ⟶ V` be a surjective and flat
1-morphism of algebraic stacks which is locally of finite presentation. Then there is a finite
surjective morphism `g : Y' ⟶ Y` of algebraic spaces such that `V' = g⁻¹(V) ⟶ V` factors Zariski
locally through `f`: there are open immersions `ι j : W j ⟶ Y'` contained in `g⁻¹(V)` (they
factor through `V` over `g`, by `q j`) whose images cover `g⁻¹(V)`, and 1-morphisms
`x j : W j ⟶ 𝒳` with `x j ≫ f` 2-isomorphic to `q j`.

The proof is the source's second paragraph: [Stacks, Proposition 09YC] (in the form
`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`) gives a finite
surjective `π : h_{Y₁} ⟶ Y` from a scheme of the site; `Y₁` is quasi-compact and
quasi-separated, `π⁻¹(V)` is a quasi-compact open of `h_{Y₁}`, and the base change of `f` to it is
again surjective, flat and locally of finite presentation. The scheme case,
`AlgebraicGeometry.Stack.exists_finite_surjective_zariskiLocal_factorization_of_yoneda`
([Stacks, Tag 0CP0] and [Stacks, Tag 0CNY]), then gives a finite surjective `Y' ⟶ h_{Y₁}`, and
its composite with `π` is the required `g`. -/
@[stacks 0CQ6 "Chow's lemma for algebraic stacks: a flat surjection locally of finite \
presentation onto a quasi-compact open of a qcqs algebraic space splits Zariski locally after a \
finite surjective base change."]
theorem exists_finite_surjective_zariskiLocal_factorization
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
    (hfs : IsSurjective B S hS f) (hff : AlgebraicStacks.IsFlat B S hS f)
    (hfl : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
      Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
      ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
        (q : ∀ j, W j ⟶ V.toFunctor)
        (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
        (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
        (∀ y : Space.points B S hS Y',
          Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
            ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
        ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)) :=
  exists_finite_surjective_zariskiLocal_factorization_of_finiteSchemeCover B S hS
    (fun Z hZ hZqc hZqs => Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS
      B.contains_terminal Z hZ hZqc hZqs)
    hY hYqc hYqs V hV hVqc f hfs hff hfl

end AlgebraicGeometry.Stack

end
