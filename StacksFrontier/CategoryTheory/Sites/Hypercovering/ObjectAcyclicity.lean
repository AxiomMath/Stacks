module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AugmentedAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexOver

/-!
# Homology of the simplicial presheaf of a hypercovering

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a hypercovering
of `X`. The simplicial presheaf represented by `K` has zero homology sheaf in every positive
degree, while its degree-zero homology sheaf is the free abelian sheaf on the representable
presheaf of `X`.

## Main results

* `isZero_sheafHomology_of_isHypercovering`: positive-degree vanishing.
* `sheafHomologyZeroIso_of_isHypercovering`: the degree-zero homology sheaf is the free abelian
  sheaf on the presheaf represented by `X`.

## Implementation notes

The source's `F(K)` is obtained by evaluating each formal coproduct after forgetting the maps to
`X`, which is `SectionsOver.associatedSimplicialPresheaf`. Vanishing is expressed by `IsZero`, and
the identification in degree zero by the canonical isomorphism supplied by the result.

Both statements are Tag 01GE applied to the augmented simplicial presheaf of `K`: Tag 01G9 says
that its degree-zero augmentation, its relation map and all its higher matching maps are locally
surjective, which are exactly the hypotheses Tag 01GE asks for. The relation map of Tag 01GE is
`CategoryTheory.SimplicialObject.Augmented.edgesToFiberProduct`, which is the one-simplex matching
map `oneMatchingMap` of Tag 09VU — the two agree because both are determined by their composites
with the two fibre-product projections, namely the two face maps.

## References

* [Stacks Project, Tag 01GF](https://stacks.math.columbia.edu/tag/01GF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

section

variable (J : Pretopology C) {X : C}
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

omit [HasPullbacks C] [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] in
/-- The relation map of Tag 01GE for the augmented simplicial presheaf of a simplicial
semi-representable object is its one-simplex matching map of Tag 09VU. -/
theorem edgesToFiberProduct_eq_oneMatchingMap :
    oneMatchingMap (associatedAugmentedSimplicialPresheafOver.{w} K).left
        (associatedAugmentedSimplicialPresheafOver.{w} K).right
        (associatedAugmentedSimplicialPresheafOver.{w} K).hom =
      SimplicialObject.Augmented.edgesToFiberProduct
        (associatedAugmentedSimplicialPresheafOver.{w} K) := by
  apply pullback.hom_ext <;>
    simp [oneMatchingMap, SimplicialObject.Augmented.edgesToFiberProduct]

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] in
/-- The three local-surjectivity hypotheses of Tag 01GE, for the augmented simplicial presheaf of
a hypercovering. -/
theorem isLocallySurjective_of_isHypercovering (hK : IsHypercovering J K) :
    Presheaf.IsLocallySurjective J.toGrothendieck
        ((associatedAugmentedSimplicialPresheafOver.{w} K).hom.app
          (Opposite.op (SimplexCategory.mk 0))) ∧
      Presheaf.IsLocallySurjective J.toGrothendieck
        (SimplicialObject.Augmented.edgesToFiberProduct
          (associatedAugmentedSimplicialPresheafOver.{w} K)) ∧
      ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J.toGrothendieck
        (((SimplicialObject.coskAdj n).unit.app
          (associatedAugmentedSimplicialPresheafOver.{w} K).left).app
            (Opposite.op (SimplexCategory.mk (n + 1)))) :=
  ⟨locallySurjective_augmentation_of_isHypercovering J K hK,
    edgesToFiberProduct_eq_oneMatchingMap K ▸
      locallySurjective_oneMatchingMap_of_isHypercovering J K hK,
    fun n hn ↦ locallySurjective_higherMatchingMap_of_isHypercovering J K hK n hn⟩

/-- **Stacks Project, Tag 01GF (positive degrees).** The homology of the simplicial presheaf
associated to a hypercovering vanishes in every positive degree. -/
@[stacks 01GF "positive-degree vanishing", sga "4 V 7.3.2" "3) positive degrees"]
theorem isZero_sheafHomology_of_isHypercovering (hK : IsHypercovering J K) (i : ℕ) (hi : 0 < i) :
    IsZero (SimplicialObject.sheafHomology J.toGrothendieck
      (SectionsOver.associatedSimplicialPresheaf.{w} K) i) :=
  let h := isLocallySurjective_of_isHypercovering J K hK
  SimplicialObject.Augmented.isZero_sheafHomology_of_isLocallySurjective_matchingMaps
    J.toGrothendieck (associatedAugmentedSimplicialPresheafOver.{w} K) h.1 h.2.1 h.2.2 i hi

/-- **Stacks Project, Tag 01GF (degree zero).** The degree-zero homology of the simplicial
presheaf associated to a hypercovering is the free abelian sheaf on the represented object. -/
@[stacks 01GF "degree-zero identification", sga "4 V 7.3.2" "3) degree zero"]
noncomputable def sheafHomologyZeroIso_of_isHypercovering (hK : IsHypercovering J K) :
    SimplicialObject.sheafHomology J.toGrothendieck
        (SectionsOver.associatedSimplicialPresheaf.{w} K) 0 ≅
      (presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
        (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) :=
  let h := isLocallySurjective_of_isHypercovering J K hK
  SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps
    J.toGrothendieck (associatedAugmentedSimplicialPresheafOver.{w} K) h.1 h.2.1 h.2.2

end

end Stacks.CategoryTheory.Hypercovering

end
