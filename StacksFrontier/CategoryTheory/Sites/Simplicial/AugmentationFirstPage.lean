module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentDerivedSections
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# The first-page term of the spectral sequence of an augmented simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and let `a` be an augmentation of `S`
towards a site `(D, K)` (Stacks 0D6Z). Stacks 0D7A asserts, for `K` in `D^+(C_total)`, a
spectral sequence with

```
E_1^{p,q} = R^q a_{p,*} K_p  ⇒  R^{p+q} a_* K
```

functorially in `K`. This file builds the first-page **term** of that display and proves that
it is the term the source writes: the restriction `(-)_p` to the component of simplicial
degree `p` followed by the `q`-th right derived functor of the direct image `a_{p,*}` along the
component augmentation of Stacks 0D70 — and *not* the `q`-th right derived functor of the
composite `a_{p,*}((-)_p)`. The two agree, which is what makes the display legitimate.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.restrictAb`: restriction of
  abelian sheaves on the total site to the component of a simplicial degree.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentAugmentationPushforwardAb`: the
  direct image `a_{p,*}` of abelian sheaves along the component augmentation of Stacks 0D70.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentHigherDirectImage`: the higher
  direct image `R^q a_{p,*}`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.firstPageTerm`: the first-page term
  `R^q a_{p,*}(-)_p`, as a functor of an abelian sheaf on the total site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.totalHigherDirectImage`: the higher
  direct image `R^m a_*` along the total augmentation, the abutment of the source's display.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.firstPageTermIso`: **the first-page term
  is `R^q a_{p,*} K_p`**, the derived functor of `a_{p,*}` applied to the restriction, and this
  agrees with the derived functor of the composite `a_{p,*}((-)_p)`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.additive_componentAugmentationPushforwardAb`
  and `.additive_abelianTotalPushforward`: the component and total direct images of abelian
  sheaves are additive, being right adjoints.

## Implementation notes

The agreement of the two readings of the term is
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, whose hypotheses on the first
factor are exactness and preservation of injective objects. For restriction to a simplicial
component both are available: exactness because restriction has a left adjoint (lower shriek,
Stacks 09WG) and a right adjoint (the direct image of the cocontinuous component inclusion),
and preservation of injectives is Stacks 09WH. They are consumed here at the spelling
`CategoryTheory.Functor.sheafPushforwardContinuous` at which
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentDerivedSections.lean` states them.

Additivity of a direct image of abelian sheaves along a morphism of topoi follows from its
preservation of limits as a right adjoint, by way of binary products; no alternative of
Stacks 04DB is needed for it.

Degrees are indexed by `ℕ`, which is the indexing of
`CategoryTheory.Functor.rightDerived`; the term is a functor of an abelian sheaf on the total
site rather than of an object of `D^+(C_total)`, as for the topological analogue
`Stacks.Topology.Simplicial.cohomologySpectralSequence` of Stacks 09W6.

The spectral sequence of Stacks 0D7A, for an object of `D⁺(C_total)`, with its first page
identified with `R^q a_{p,*} K_p` and its abutment `R^{p+q} a_* K`, is
`CategoryTheory.SimplicialSiteSituation.Augmentation.higherDirectImageSpectralSequence` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationDerivedSpectralSequence.lean`.

## References

* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CompositeRightDerived
open Stacks.Topos.AbelianPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- The direct image `a_{n,*}` of abelian sheaves along the augmentation of the simplicial
degree `n`, the morphism of topoi of Stacks 0D70, part (1). -/
abbrev componentAugmentationPushforwardAb [HasSheafify K Ab.{u}] :
    Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf K Ab.{u} :=
  abelianPushforward (S.componentTopology n) (componentAugmentation S D K a n)

variable [HasSheafify K Ab.{u}]

/-- The direct image along a component augmentation is additive, being a right adjoint. -/
instance additive_componentAugmentationPushforwardAb :
    (componentAugmentationPushforwardAb S D K a n).Additive := by
  let := preservesLimitsOfSize_abelianPushforward
    (S.componentTopology n) (componentAugmentation S D K a n)
  let : PreservesFiniteLimits (componentAugmentationPushforwardAb S D K a n) := inferInstance
  exact Functor.additive_of_preserves_binary_products _

/-- The direct image along the total augmentation is additive, being a right adjoint. -/
instance additive_abelianTotalPushforward :
    (abelianTotalPushforward S D K a).Additive := by
  let := preservesLimitsOfSize_abelianPushforward
    S.totalTopology (totalMorphismOfTopoi S D K a)
  let : PreservesFiniteLimits
      (abelianPushforward S.totalTopology (totalMorphismOfTopoi S D K a)) := inferInstance
  exact Functor.additive_of_preserves_binary_products
    (abelianPushforward S.totalTopology (totalMorphismOfTopoi S D K a))

/-- The higher direct image `R^q a_{n,*}` along the augmentation of the simplicial degree `n`. -/
abbrev componentHigherDirectImage (q : ℕ) :
    Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf K Ab.{u} :=
  (componentAugmentationPushforwardAb S D K a n).rightDerived q

/-- The higher direct image `R^m a_*` along the total augmentation of Stacks 0D70: the abutment
of the display of Stacks 0D7A. -/
abbrev totalHigherDirectImage (m : ℕ) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u} :=
  (abelianTotalPushforward S D K a).rightDerived m

/-- The first-page term `R^q a_{n,*} K_n` of Stacks 0D7A: restriction to the component of
simplicial degree `n`, followed by the `q`-th higher direct image along the augmentation of that
degree. -/
abbrev firstPageTerm (q : ℕ) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u} :=
  restrictAb S n ⋙ componentHigherDirectImage S D K a n q

/-- **The first-page term of Stacks 0D7A.** The `q`-th right derived functor of the composite
`a_{n,*}((-)_n)` is the restriction to the component of simplicial degree `n` followed by the
`q`-th higher direct image `R^q a_{n,*}`; so the first-page term of the source's display is the
term `R^q a_{n,*} K_n` it writes, and not the derived functor of a composite.

Restriction to a component is exact and preserves injective abelian sheaves (Stacks 09WH), which
is what the comparison of right derived functors needs. -/
def firstPageTermIso (q : ℕ) :
    (restrictAb S n ⋙ componentAugmentationPushforwardAb S D K a n).rightDerived q ≅
      firstPageTerm S D K a n q :=
  compRightDerivedNatIso (restrictAb S n)
    (componentAugmentationPushforwardAb S D K a n) q

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
