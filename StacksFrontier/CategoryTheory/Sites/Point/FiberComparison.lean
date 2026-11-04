module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.CategoryTheory.Sites.Point.Defs

/-!
# Comparing the stalk functor of a point of a topos with that of a point of the site

Let `p` be a point of the topos `Sh(C, J)` and let `Φ` be a point of the site `(C, J)`. Both
`p` and `Φ` come with an adjoint pair: `p⁻¹ ⊣ p_*` by definition of a morphism of topoi, and
`Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor` by Mathlib's
`GrothendieckTopology.Point.skyscraperSheafAdjunction`. Two adjoint pairs between the same two
categories have conjugate mates: a natural transformation between the right adjoints
corresponds to one between the left adjoints, in the opposite direction, and one is an
isomorphism exactly when the other is.

Specialised to this situation, a comparison `p_* ⟶ Φ.skyscraperSheafFunctor` of skyscraper
functors is the same thing as a comparison `Φ.sheafFiber ⟶ p⁻¹` of stalk functors, and an
identification of the two pushforwards is the same thing as an identification of the two inverse
images.

## Main definitions

* `PointOfTopos.sheafFiberComparison`: the mate `Φ.sheafFiber ⟶ p⁻¹` of a natural
  transformation `p_* ⟶ Φ.skyscraperSheafFunctor`.
* `PointOfTopos.sheafFiberComparisonIso`: the same construction for isomorphisms.

## Main results

* `PointOfTopos.isIso_sheafFiberComparison_of_isIso`: the comparison of stalk functors is an
  isomorphism as soon as the comparison of skyscraper functors is one.
* `PointOfTopos.isIso_of_isIso_sheafFiberComparison`: the converse.

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace PointOfTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (p : PointOfTopos.{w, v, u} J) (Φ : GrothendieckTopology.Point.{w} J)

/-- The comparison of stalk functors attached to a comparison of skyscraper functors.

Given a point `p` of the topos `Sh(C, J)`, a point `Φ` of the site `(C, J)` and a natural
transformation `α : p_* ⟶ Φ.skyscraperSheafFunctor` between their pushforwards, this is the
conjugate (mate) natural transformation `Φ.sheafFiber ⟶ p⁻¹` between their stalk functors,
formed from the adjunctions `p⁻¹ ⊣ p_*` and
`Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor`. -/
noncomputable def sheafFiberComparison (α : p.pushforward ⟶ Φ.skyscraperSheafFunctor) :
    Φ.sheafFiber ⟶ p.inverseImage :=
  (conjugateEquiv p.adj Φ.skyscraperSheafAdjunction).symm α

/-- The comparison of stalk functors is an isomorphism whenever the comparison of skyscraper
functors it comes from is one: conjugation of mates between two adjoint pairs preserves
isomorphisms. -/
instance isIso_sheafFiberComparison_of_isIso (α : p.pushforward ⟶ Φ.skyscraperSheafFunctor)
    [IsIso α] :
    IsIso (p.sheafFiberComparison Φ α) :=
  inferInstanceAs (IsIso ((conjugateEquiv p.adj Φ.skyscraperSheafAdjunction).symm α))

/-- Conversely, if the comparison of stalk functors is an isomorphism then so is the comparison
of skyscraper functors it comes from: conjugation of mates also reflects isomorphisms. -/
theorem isIso_of_isIso_sheafFiberComparison (α : p.pushforward ⟶ Φ.skyscraperSheafFunctor)
    (h : IsIso (p.sheafFiberComparison Φ α)) : IsIso α :=
  haveI : IsIso ((conjugateEquiv p.adj Φ.skyscraperSheafAdjunction).symm α) := h
  conjugateEquiv_symm_of_iso p.adj Φ.skyscraperSheafAdjunction α

/-- An isomorphism `p_* ≅ Φ.skyscraperSheafFunctor` of skyscraper functors induces an
isomorphism `Φ.sheafFiber ≅ p⁻¹` of stalk functors, whose underlying morphism is
`PointOfTopos.sheafFiberComparison`. -/
@[simps! hom]
noncomputable def sheafFiberComparisonIso (α : p.pushforward ≅ Φ.skyscraperSheafFunctor) :
    Φ.sheafFiber ≅ p.inverseImage :=
  (conjugateIsoEquiv p.adj Φ.skyscraperSheafAdjunction).symm α

end PointOfTopos
