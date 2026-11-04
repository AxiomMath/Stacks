module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationFirstPage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites

/-!
# The direct image of a simplicial component as a functor of abelian sheaves

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The degree-`n` term of the complex of Stacks 0D79 is
`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianComponentPushforward`, the functor
`F ↦ a_{n,*}F_n` obtained by reading the composite `a_{n,*}((-)_n)` of sheaves of sets through
the passage of Stacks 04DB. The first-page term of Stacks 0D7A is instead the composite of
`restrictAb` with `componentAugmentationPushforwardAb` formed on abelian sheaves. The two are
*not* definitionally equal — the first carries the oplax monoidal comparisons of the set-level
restriction, the second does not.

This file supplies their identification: the comparison of Stacks 04DB for the restriction
`g_n^{-1}` to a simplicial component, and the consequence that the `q`-th right derived functor
of the degree-`n` term of the complex of Stacks 0D79 is the first-page term `R^q a_{n,*} F_n`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentRestrictionAbIso`: **the
  Stacks 04DB comparison for `g_n^{-1}`**: internalizing an abelian sheaf on the total site,
  restricting the resulting commutative group object to the component of simplicial degree `n`
  and reading the operations off on sections again is the restriction of abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.internalRestrictIso`: the same comparison
  on the group-object side.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianComponentPushforwardIso`: the
  degree-`n` term of the complex of Stacks 0D79 is the composite
  `restrictAb S n ⋙ componentAugmentationPushforwardAb`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.rightDerivedAbelianComponentPushforwardIso`:
  its `q`-th right derived functor is the first-page term `R^q a_{n,*} F_n` of Stacks 0D7A.

## Implementation notes

`componentRestrictionAbIso` is `Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`, the
repository's form of Stacks 00YT at the sheaf level, applied to the inclusion of the component of
Stacks 09WG. Two things make that reuse possible. First, the direct images of abelian sheaves
occurring here are built from the same identification of abelian sheaves with commutative group
objects, `CategoryTheory.Sites.AbelianSheaf.internalSheaf`, that the comparison is stated for;
`abelianComponentPushforward_eq` and `componentAugmentationPushforwardAb_eq` record
the two unfoldings this needs. Second, the monoidal and braided instances must be *the same
terms* as the ones `abelianSheafPushforwardIso` was elaborated with, which is why the local
instances of `Stacks.Sites.AbelianPullback` are reused by name rather than redeclared: with the
braided structure of the restriction obtained through a different route the comparison's type is
still correct but its unification against the statement here exceeds the `isDefEq` budget.

The restriction is spelled `restrictSets`, as the direct image of the component inclusion, rather
than as `CategoryTheory.SimplicialSiteSituation.restrict`, so that the instances fire at the same
spelling.

## References

* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.braidedSheafToPresheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Functor.Braided.ofChosenFiniteProducts

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- Restriction of sheaves of sets to the component of simplicial degree `n`, spelled as the
direct image along the component inclusion. -/
abbrev restrictSets : Sheaf S.totalTopology (Type u) ⥤ Sheaf (S.componentTopology n) (Type u) :=
  (componentFunctor S n).sheafPushforwardContinuous (Type u) (S.componentTopology n)
    S.totalTopology

/-- The degree-`n` term of the complex of Stacks 0D79, unfolded: the conjugation of the
composite of the restriction of sheaves of sets with the direct image of the component
augmentation. -/
theorem abelianComponentPushforward_eq :
    abelianComponentPushforward S D K a n =
      Sites.AbelianSheaf.internalSheaf S.totalTopology ⋙
        (restrictSets S n ⋙ (componentAugmentation S D K a n).pushforward).mapCommGrp ⋙
          Sites.AbelianSheaf.externalSheaf K :=
  rfl

/-- The direct image of abelian sheaves along the component augmentation, unfolded. -/
theorem componentAugmentationPushforwardAb_eq [HasSheafify K AddCommGrpCat.{u}] :
    componentAugmentationPushforwardAb S D K a n =
      Sites.AbelianSheaf.internalSheaf (S.componentTopology n) ⋙
        ((componentAugmentation S D K a n).pushforward).mapCommGrp ⋙
          Sites.AbelianSheaf.externalSheaf K :=
  rfl

/-- **The comparison of Stacks 04DB for the restriction `g_n^{-1}` to a simplicial component.**
Internalizing the group operations of an abelian sheaf on the total site, restricting the
resulting commutative group object to the component of simplicial degree `n` and reading the
operations off on sections again gives the restriction of abelian sheaves. -/
def componentRestrictionAbIso :
    Sites.AbelianSheaf.internalSheaf S.totalTopology ⋙ (restrictSets S n).mapCommGrp ⋙
        Sites.AbelianSheaf.externalSheaf (S.componentTopology n) ≅
      restrictAb S n :=
  Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso (componentFunctor S n)
    (S.componentTopology n) S.totalTopology

/-- Internalizing an abelian sheaf on the total site and restricting the resulting commutative
group object to the component of simplicial degree `n` is restricting the abelian sheaf and then
internalizing. -/
def internalRestrictIso :
    Sites.AbelianSheaf.internalSheaf S.totalTopology ⋙ (restrictSets S n).mapCommGrp ≅
      restrictAb S n ⋙ Sites.AbelianSheaf.internalSheaf (S.componentTopology n) :=
  Functor.isoWhiskerLeft
      (Sites.AbelianSheaf.internalSheaf S.totalTopology ⋙ (restrictSets S n).mapCommGrp)
      (Sites.AbelianSheaf.externalInternalIso (S.componentTopology n)).symm ≪≫
    Functor.isoWhiskerRight (componentRestrictionAbIso S n)
      (Sites.AbelianSheaf.internalSheaf (S.componentTopology n))

variable [HasSheafify K AddCommGrpCat.{u}]

/-- **The terms of the complex of Stacks 0D79, read on abelian sheaves.** The degree-`n` term
`F ↦ a_{n,*}F_n` of the complex of Stacks 0D79, which is the conjugation of the set-level
composite through the passage of Stacks 04DB, is the composite of the restriction of abelian
sheaves to the component of simplicial degree `n` with the direct image of abelian sheaves along
the augmentation of that degree. -/
def abelianComponentPushforwardIso :
    abelianComponentPushforward S D K a n ≅
      restrictAb S n ⋙ componentAugmentationPushforwardAb S D K a n :=
  Functor.isoWhiskerLeft (Sites.AbelianSheaf.internalSheaf S.totalTopology)
      (Functor.isoWhiskerRight
        (Functor.mapCommGrpCompIso (F := restrictSets S n)
          (G := (componentAugmentation S D K a n).pushforward))
        (Sites.AbelianSheaf.externalSheaf K)) ≪≫
    Functor.isoWhiskerRight (internalRestrictIso S n)
      ((componentAugmentation S D K a n).pushforward.mapCommGrp ⋙
        Sites.AbelianSheaf.externalSheaf K)

/-- The direct image `F ↦ a_{n,*}F_n` is additive. -/
instance additive_abelianComponentPushforward :
    (abelianComponentPushforward S D K a n).Additive :=
  Functor.additive_of_iso (abelianComponentPushforwardIso S D K a n).symm

/-- **The first-page term of Stacks 0D7A, attached to the double complex of Stacks 0D79.** The
`q`-th right derived functor of the degree-`n` term `F ↦ a_{n,*}F_n` of the complex of
Stacks 0D79 is the `q`-th higher direct image `R^q a_{n,*}` applied to the restriction `F_n` to
the component of simplicial degree `n`. The spectral sequence itself is
`CategoryTheory.SimplicialSiteSituation.Augmentation.higherDirectImageSpectralSequence`. -/
def rightDerivedAbelianComponentPushforwardIso (q : ℕ) :
    (abelianComponentPushforward S D K a n).rightDerived q ≅ firstPageTerm S D K a n q :=
  Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (abelianComponentPushforwardIso S D K a n) q ≪≫
    firstPageTermIso S D K a n q

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
