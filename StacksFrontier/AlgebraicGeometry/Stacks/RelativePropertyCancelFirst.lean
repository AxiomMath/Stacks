module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Cancelling the first factor of a relative property

Let `S` be a scheme contained in a big fppf site `B`, let `P`, `R₁` and `R₂` be properties of
morphisms of algebraic spaces over `S`, and let `i : 𝒳 ⟶ 𝒳'` and `q : 𝒳' ⟶ 𝒴` be 1-morphisms of
categories fibred in groupoids over the big fppf site of `S`. This file proves that the condition
of Properties of Stacks, Section 04XB, cancels its *first* factor: if `i ≫ q` satisfies the
condition for `P`, `i` satisfies it for `R₁` and for `R₂`, and `P` cancels against the pair for
morphisms of algebraic spaces — a composite `a ≫ b` with `P (a ≫ b)`, `R₁ a` and `R₂ a` has
`P b` — then `q` satisfies the condition for `P`.

Two properties of the first factor rather than one, because the case this is written for has
`i` a thickening, whose two clauses — being a closed immersion and being surjective — are
separate properties of morphisms of algebraic spaces, each with its own base-change and locality
instances.

This is the companion of `AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`, which cancels
the second factor, and the two are not proved the same way. The second-factor statement tests
`f` at points of the intermediate stack `𝒴`, which are also points of `𝒵`, so the two base
changes compared live over one scheme; here the test for `q` is at points of `𝒴` and the test
for `i` is at points of `𝒳'`, and the comparison morphism is a base change of `i` along a
1-morphism out of a stack which is *representable by an algebraic space* but is not a scheme.
**Stacks 04XC**
(`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`) is exactly what makes
that test legitimate, so the whole argument runs at the level of 2-fibre product squares and
never unfolds the quantifier of Stacks 03YK.

The shape is: fix a stack `𝒵` representable by an algebraic space, a 1-morphism `g : 𝒵 ⟶ 𝒴` and
a 2-fibre product `Q` of the cospan `(g, q)`; its apex is representable by an algebraic space,
and the base change `R₀` of `i` along `Q.snd` has apex representable by an algebraic space too
(**Stacks 0300**). Pasting `Q` and `R₀`
(`CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`) presents that apex as a 2-fibre product
of the cospan `(g, i ≫ q)` whose first projection is `R₀.fst ≫ Q.fst`, so Stacks 04XC applied
to `i ≫ q` gives `P` of the representing morphism of that composite, and applied to `i` gives
`R₁` and `R₂` of the representing morphism of `R₀.fst`. The identification of Stacks 04SW is
functorial
(`AlgebraicGeometry.Stack.representingMap_comp`), so those two are a composite and its first
factor, and the cancellation hypothesis gives `P` of the representing morphism of `Q.fst` —
which, quantified over all such `𝒵`, `g` and `Q`, is the condition for `q` by the easy half of
Stacks 04XC.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst`: the statement
  above.

## Implementation notes

Each of `P`, `R₁` and `R₂` carries the two instance arguments of
`AlgebraicGeometry.Stack.HasRelativeProperty`, stability under base change and locality at the
target for the fppf precoverage, because the statement mentions that abbreviation for each of
them; the argument itself uses them only through Stacks 04XC.

No hypothesis beyond representability by algebraic spaces is placed on `i`, `q` or `i ≫ q`, and
the algebraicity of the three stacks is not used: as in
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange`, only the fibred
categories enter.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A condition of Stacks 04XB cancels the first factor of a composite.** Let `P`, `R₁` and
`R₂` be properties of morphisms of algebraic spaces over `S` and suppose that `P` cancels against
the pair: a composite `a ≫ b` of morphisms of algebraic spaces with `P (a ≫ b)`, `R₁ a` and
`R₂ a` has `P b`. If two composable 1-morphisms of categories fibred in groupoids over the big
fppf site of `S` are such that `i`, `q` and `i ≫ q` are representable by algebraic spaces,
`i ≫ q` satisfies the condition of Stacks 04XB for `P` and `i` satisfies it for `R₁` and for
`R₂`, then `q` satisfies it for `P`.

This is the companion of `AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`; see the
implementation notes of this file for why it runs through **Stacks 04XC** rather than through
the quantifier of Stacks 03YK. -/
theorem hasRelativeProperty_of_comp_of_spaceCancelFirst
    (P R₁ R₂ : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    [R₁.IsStableUnderBaseChange]
    [R₁.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    [R₂.IsStableUnderBaseChange]
    [R₂.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    (hcancel : ∀ {A C D : AlgebraicSpaces B S hS} (a : A ⟶ C) (b : C ⟶ D),
      P (a ≫ b) → R₁ a → R₂ a → P b)
    {𝒳 𝒳' 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (i : 𝒳 ⟶ 𝒳') (q : 𝒳' ⟶ 𝒴)
    (hi : IsRepresentableByAlgebraicSpaces B S hS i.hom)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom)
    (hiq : IsRepresentableByAlgebraicSpaces B S hS (i ≫ q).hom)
    (hR₁ : HasRelativeProperty B S hS R₁ i hi)
    (hR₂ : HasRelativeProperty B S hS R₂ i hi)
    (hP : HasRelativeProperty B S hS P (i ≫ q) hiq) :
    HasRelativeProperty B S hS P q hq := by
  refine hasRelativeProperty_of_forall_space_baseChange B S hS P q hq ?_
  intro 𝒵 _h𝒵 g Q hQ F G hF hG eF eG
  -- the base change of `i` along the second projection of `Q`
  obtain ⟨E, hE, ⟨eE⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS 𝒳 𝒳' Q.pt i Q.snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd i)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.snd i)
      hi ⟨F, hF, ⟨eF⟩⟩
  -- Stacks 04XC at `i`: the comparison of the two base changes has `R₁` and `R₂`
  have hRm := fun (R : MorphismProperty (AlgebraicSpaces B S hS)) [R.IsStableUnderBaseChange]
      [R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
      (hR : HasRelativeProperty B S hS R i hi) =>
    prop_representingMap_of_hasRelativeProperty.{u, v} B S hS R i hi hR Q.pt Q.snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd i)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.snd i)
      E F hE hF eE eF
  -- Stacks 04XC at `i ≫ q`, read on the pasted rectangle
  have hPm := prop_representingMap_of_hasRelativeProperty.{u, v} B S hS P (i ≫ q) hiq hP 𝒵 g
    (Q.pasteSnd (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd i))
    (Bicategory.isTwoFibreProduct_pasteSnd Q hQ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd i)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.snd i))
    E G hE hG eE eG
  rw [show (Q.pasteSnd (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.snd i)).fst =
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd i).fst ≫ Q.fst from
    rfl, representingMap_comp B S hS E F G eE eF eG _ Q.fst] at hPm
  exact hcancel _ _ hPm (hRm R₁ hR₁) (hRm R₂ hR₂)

end AlgebraicGeometry.Stack

end
