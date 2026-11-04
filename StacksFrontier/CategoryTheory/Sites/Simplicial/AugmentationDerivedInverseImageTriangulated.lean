module

public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.CategoryTheory.Triangulated.LeftDerivedOfInverting

/-!
# The derived inverse image along a total augmentation is an exact functor

Let `S` be a simplicial-site situation and let `a` be an augmentation of `S` towards a site
`(D, K)`. The derived inverse image `a⁻¹ : D(D, K) ⟶ D((C/K)_total)` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean` is the
*total left derived functor* of the degreewise inverse image of abelian sheaves. This module
records that it is an exact functor of triangulated categories: it commutes with the shift and
it carries distinguished triangles to distinguished triangles.

Nothing here is specific to the augmentation. The degreewise inverse image is exact, so it
already inverts the quasi-isomorphisms, and the two conclusions are the two general statements

* `StacksDraft.PseudoCoherence.leftDerivedCommShift`: any total left derived functor commutes
  with the shift, and
* `CategoryTheory.Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts`: a total left
  derived functor of a *triangulated* functor which inverts `W` is triangulated,

applied to it.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.commShift_derivedTotalInverseImage`:
  **`a⁻¹` commutes with the shift.**
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isTriangulated_derivedTotalInverseImage`:
  **`a⁻¹` is a triangulated functor.**

Both are instances, which is what consumers of the derived augmentation adjunction need: a
statement about the bounded below derived category, or about a triangulated subcategory of the
total site, is not even well formed until `a⁻¹` is known to be exact.

## Implementation notes

The commutation of the comparison
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImageComparison` with
the shift is registered as an instance as well, since
`CategoryTheory.Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts` asks for it and it is
the shape in which a left derived functor's exactness is always proved; it is
`CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift`, whose commutation
isomorphisms on `a⁻¹` are by construction the ones of
`commShift_derivedTotalInverseImage`.

The hypothesis `W.IsInvertedBy` is
`CategoryTheory.SimplicialSiteSituation.Augmentation.inverseImageInverts`, stated there for the
resolving datum `⊤` and so taking two `trivial` arguments.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The derived inverse image along the total augmentation commutes with the shift.** It is a
total left derived functor, and every total left derived functor does. -/
instance commShift_derivedTotalInverseImage :
    (derivedTotalInverseImage S D K a).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedTotalInverseImage S D K a)
    (derivedTotalInverseImageComparison S D K a)
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) ℤ

/-- The canonical comparison from the derived inverse image to the degreewise one is compatible
with `commShift_derivedTotalInverseImage`. -/
instance natTransCommShift_derivedTotalInverseImageComparison :
    NatTrans.CommShift (derivedTotalInverseImageComparison S D K a) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (derivedTotalInverseImage S D K a)
    (derivedTotalInverseImageComparison S D K a)
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) ℤ

/-- **The derived inverse image along the total augmentation is a triangulated functor.**

The degreewise inverse image is exact, so it inverts the quasi-isomorphisms, and a total left
derived functor of a triangulated functor which inverts the localizing class is triangulated. -/
instance isTriangulated_derivedTotalInverseImage :
    (derivedTotalInverseImage S D K a).IsTriangulated :=
  Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts (derivedTotalInverseImage S D K a)
    (derivedTotalInverseImageComparison S D K a)
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (fun _ _ s hs => inverseImageInverts S D K a s hs trivial trivial)

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
