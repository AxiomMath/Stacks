module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionSquareIndependence

/-!
# Every isomorphism of representing presheaves is a comparison isomorphism (Stacks 04SW)

A category fibred in groupoids `𝒲` over the big fppf site of `S` presented by a presheaf `F` —
an equivalence over the site between `𝒲` and the category of elements of `F`, which is how
**Stacks 04SW** is recorded here — is never presented in only one way. Given one presentation `e`
by `F` and *any* isomorphism `β : F ≅ F'` of presheaves, composing `e` with the equivalence of
categories of elements that `β` induces presents `𝒲` by `F'`, and the comparison isomorphism
`AlgebraicGeometry.Stack.representingIso` of the two presentations is `β` on the nose. So the
comparison isomorphism of two presentations is not merely "possibly nontrivial": it takes every
value an isomorphism of presheaves can take, and for `F' = F` every automorphism of `F` is the
comparison automorphism of two presentations of `𝒲` by `F`.

Nothing prevents this, because a presentation is an equivalence *over the site* and nothing more
(`StacksRepresentableCFG.EquivalenceOver`); no compatibility with any further 1-morphism out of
`𝒲` is part of it.

## Main results

* `AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso`
* `AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso_symm`

## Why this is in the library: the quantifier it rules out in Stacks 0DS9 and 0DSA

The conditions of **Stacks 0DS9**, and with them the definition of **Stacks 0DSA**
(`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`,
`AlgebraicGeometry.Stack.HasLocalRingDimensionAtEveryChart`), read the invariant
`2 dim(𝒪_{V,ν}) - dim(𝒪_{R, e(ν)})` through an identification of the chart `V` with the presheaf
it represents, and state their side conditions on `ν` — finite-typeness, and lying over `x` —
through the *canonical* one, `AlgebraicGeometry.Stack.representedChartPointMap` being defined at
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`. Both therefore fix that
identification to the canonical one.

It is natural to quantify over it instead. The
result below is what makes that wrong rather than merely redundant. Combined with
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence`, it says that
reading the invariant through the presentation twisted by an automorphism `β` of `yoneda.obj V`
is reading it canonically at `β(ν)` — a point of `V` the side conditions say nothing about, lying
over a point of `|𝒳|` other than `x`. Hence:

* with an `∃`, condition (1) is satisfied by more than one integer, so Stacks 0DSA would define
  nothing;
* with a `∀`, condition (2) would demand the invariant at every point of the orbit of `ν` under
  the automorphisms of `V`, and `(1) ⇒ (2)` would be false.

The counterexample — `𝒳 = 𝐀¹ ⊔ pt`, `V = 𝐀¹ ⊔ 𝐀¹`, the swap automorphism, two values `0` and
`1` at one point — is recorded with the definition, in the module documentation of
`StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionChartIndependence.lean`. By Yoneda the
automorphisms of `yoneda.obj V` are `yoneda.map` of the automorphisms of `V` in the site, so the
orbit is as large as `Aut(V)`.

By contrast the *remaining* comparison data of a presented self-intersection — the 2-fibre
product square, the presenting algebraic space, its equivalence and the mediating morphism giving
the diagonal — is quantified over in both conditions and genuinely drops out, with no transport
of the point of the chart: that is
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`.

## Implementation notes

`CategoryTheory.PresheafOfCategories.equivalenceOverOfIso` is the equivalence of categories of
elements over the site attached to an isomorphism of presheaves, and
`StacksRepresentableCFG.EquivalenceOver.trans` composes equivalences over the site.

The computation of the comparison isomorphism is the characterisation of Stacks 04SW by the
induced functor of categories of elements
(`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_comp_eq`): the functor induced by `β` on
categories of elements *is* the forward 1-morphism of `equivalenceOverOfIso β`, so the required
commuting square holds by `rfl`.

Only the `hom` field is computed; `CategoryTheory.Iso.ext` then gives the equality of
isomorphisms, and with it the `inv` field, which is what the reversed pair
`AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso_symm` needs —
`(representingIso F F' e e').inv` and `(representingIso F' F e' e).hom` are the same term.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Realize

variable {𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (e : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (β : F ≅ F')

/-- **The comparison isomorphism of two presentations of one category fibred in groupoids takes
every value.** Let `e` present `𝒲` by the presheaf `F`, and let `β : F ≅ F'` be any isomorphism
of presheaves. Composing `e` with the equivalence of categories of elements that `β` induces
presents `𝒲` by `F'`, and the comparison isomorphism
`AlgebraicGeometry.Stack.representingIso` of the two presentations is `β`.

A presentation is an equivalence over the site and nothing more, so this composite really is
another presentation; in particular, for `F' = F`, every automorphism of `F` arises as the
comparison automorphism of two presentations of `𝒲` by `F`. That is what rules out quantifying
over the presentation of a chart in the conditions of Stacks 0DS9 — see the module
documentation. -/
theorem representingIso_trans_equivalenceOverOfIso :
    representingIso B S hS F F' e
        (e.trans (PresheafOfCategories.equivalenceOverOfIso β)) = β :=
  Iso.ext
    (morphismSpaceEquiv_eq_of_comp_eq B S hS 𝒲 𝒲 F F' e
      (e.trans (PresheafOfCategories.equivalenceOverOfIso β)) _ β.hom rfl)

/-- The comparison isomorphism of the same two presentations read in the other order: it is the
inverse of `AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso`, the two being
the same term by the definition of `AlgebraicGeometry.Stack.representingIso`. -/
theorem representingIso_trans_equivalenceOverOfIso_symm :
    (representingIso B S hS F' F (e.trans (PresheafOfCategories.equivalenceOverOfIso β)) e).hom =
      β.inv :=
  congrArg Iso.inv (representingIso_trans_equivalenceOverOfIso B S hS F F' e β)

end Realize

end AlgebraicGeometry.Stack

end
