module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence
public import StacksFrontier.Homology.DerivedIndexing.SourceCongruenceCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr

/-!
# The abelian model bridge is the canonical bridge of `i_* R𝓗_Z^{ab}`

Let `Z` be a closed subset of a ringed space `X`.  Two isomorphisms identify the degree-`n`
cohomology sheaf of `i_* R𝓗_Z^{ab}(𝒢[0])` — the unbounded model of `i_*ℋ ⁿ_Z` — with an
`ℕ`-indexed right derived functor:

* `Stacks.Cohomology.AbelianModelComparison.abelianModelComponent`, which lands in
  `i_*(Rⁿ H_Z(𝒢))`: the exact direct image is moved past the cohomology sheaf and the unbounded
  model *on `Z`* is identified with Mathlib's `CategoryTheory.Functor.rightDerived`; and
* the canonical bridge `singleCompDerivedCompHomologyIsoRightDerived` of
  `i_* R𝓗_Z^{ab}` itself, which lands in `Rⁿ(𝒢 ↦ i_*ℋ_Z(𝒢))`, the right derived functor of the
  supported-sections **endofunctor** of abelian sheaves — the functor the two classical excisions
  of [Stacks, Tag 0G87] and the degreewise comparison
  `Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparison` speak.

The two targets are identified by
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso`, and this file
proves that the two isomorphisms agree across it.

Before this file nothing related the endofunctor's canonical bridge to the model comparison, and
`abelianLocalCohomologySheafPushforwardIso` had no consumer beyond its own excision statement.

## Main results

* `abelianSupportedPushforwardBridge_hom_app`: **the canonical bridge of `i_* R𝓗_Z^{ab}` is the
  model comparison followed by `abelianLocalCohomologySheafPushforwardIso`.**
* `abelianModelComponent_hom_comp_pushforwardIso`: the same identity read as a computation of the
  model comparison — the bridge followed by `abelianLocalCohomologySheafPushforwardIso` inverted.

## Implementation notes

**Carried hypotheses: none beyond `hZ : IsClosed Z`.**  Closedness is what makes the direct image
from `Z` exact, hence applicable through `CategoryTheory.Functor.mapDerivedCategory`; nothing is
assumed on the coefficient abelian sheaf.

The proof is three generic coherences of the library, in this order:

* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app` moves the
  bridge from the endofunctor `𝒢 ↦ i_*ℋ_Z(𝒢)` to the composite `H_Z ⋙ i_*`, which needs exactly
  the comparison `hunit` of the two units below;
* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` splits the
  bridge for that composite into `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, the
  bridge for `H_Z` under the direct image, and `CategoryTheory.Functor.rightDerivedCompIso`
  inverted — the first two being precisely the two factors of `abelianModelComponent`, by
  `Stacks.Cohomology.AbelianModelComparison.abelianModelComponent_hom` together with
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`;
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` identifies
  `abelianLocalCohomologySheafPushforwardIso` with that same
  `CategoryTheory.Functor.rightDerivedCompIso` inverted, followed by the right derived functor of
  the comparison of the two spellings of the underived functor — which is the one factor the
  source congruence contributes.

So the three coherences meet at `CategoryTheory.Functor.rightDerivedCompIso` and at
`CategoryTheory.NatTrans.rightDerived` of
`abelianSupportedSectionsRealizedCompPushforwardIso`, and nothing else has to be chased.

**The comparison of the two units.**  `derivedAbelianSupportedPushforwardUnit` and
`postcomposeUnit` are built by the same four-step recipe — the two actions
of the direct image identified, then the direct image of the unit of `R𝓗_Z^{ab}` — and differ
only in their first factor, which is
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` at
`abelianSupportedSectionsRealizedCompPushforwardIso` in the one and at `CategoryTheory.Iso.refl`
in the other.  So the comparison is the degreewise action of that isomorphism inverted, and both
sides are read off by `rfl` up to the identity morphisms the reassociations contribute.

**Why the exactness instances are introduced by `letI` and never as hypotheses.**
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward` is *defined* as
`derivedAbelianSupportedSectionsOnClosed ⋙ (abelianClosedPushforward Z).mapDerivedCategory`
under two `letI`-bound exactness instances, and `CategoryTheory.Functor.mapDerivedCategory` takes
those instances as arguments; an arbitrary instance hypothesis would give a *different* functor.
Binding the same two lemmas by `letI` makes the two terms the same term, which is what lets the
generic coherences — whose statements mention `Rw ⋙ G.mapDerivedCategory` — be applied at
`derivedAbelianSupportedPushforward` with no transport.  Each crossing of the two spellings is
confined to one `have` with its type written out, as the implementation notes of
`Stacks.Perfect.SupportedEndoForgetDegreewise` prescribe.

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.9 (Tag 0G87)](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward
  derivedAbelianSupportedPushforwardSplit derivedAbelianSupportedPushforwardUnit)
open Stacks.Cohomology.AbelianModelComparison (abelianLocalCohomologySheafOfComplexFunctorIso
  abelianModelComponent abelianModelComponent_hom abelianPushHomologySingleIso)
open Stacks.Cohomology.Localization (enoughKInjectives)
open Stacks.DerivedFunctor (isRightDerivedFunctor_postcompose postcomposeUnit postcomposeUnit_app
  singleCompDerivedCompHomologyIsoRightDerived)
open Stacks.DerivedIndexing (moduleComparison_rightDerivedCompIso_hom_app
  singleCompDerivedCompHomologyIsoRightDerived_postComp_app
  singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app)

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.abelianSheaves_isGrothendieckAbelian

/-! ### Formal rearrangements -/

/-- **The unit of a right derived functor, read off its four-step construction.**  Stated at a
variable category with the objects implicit and the morphisms explicit: the composite crosses the
two spellings `(F ⋙ G).mapHomotopyCategory` and
`F.mapHomotopyCategory ⋙ G.mapHomotopyCategory` of one functor, and at a variable category every
step is `exact` rather than a rewrite in place, which across that pair is not type-correct. -/
private theorem unit_formal {E : Type*} [Category* E] {a b c d : E} (u : a ⟶ b) (g : b ⟶ c)
    (v : c ⟶ d) (i : b ⟶ b) (j : c ⟶ c) (k : d ⟶ d) (t : b ⟶ d)
    (hi : i = CategoryStruct.id b) (hj : j = CategoryStruct.id c)
    (hk : k = CategoryStruct.id d) (ht : t = g ≫ v) :
    (u ≫ i ≫ g ≫ j) ≫ v ≫ k = u ≫ t := by
  rw [hi, hj, hk, ht]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

/-- Regrouping a three-factor composite followed by one more factor into two named halves, at an
abstract category: this is how the post-composition coherence's output is split into the model
comparison and the comparison of the two targets.  The two halves are passed as morphisms with
their computations, so that no rewrite has to be performed inside the composite. -/
private theorem assemble {E : Type*} [Category* E] {a b c d f : E} (p : a ⟶ b) (q : b ⟶ c)
    (r : c ⟶ d) (s : d ⟶ f) (m : a ⟶ c) (t : c ⟶ f) (hm : m = p ≫ q) (ht : t = r ≫ s) :
    (p ≫ q ≫ r) ≫ s = m ≫ t := by
  rw [hm, ht]
  simp only [Category.assoc]

/-! ### The composite spelling of the underived functor -/

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (n : ℕ)
  (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})

/-- **The two units of `i_* R𝓗_Z^{ab}` differ by the degreewise action of the comparison of the
two spellings of the underived functor.**  On the left `i_* R𝓗_Z^{ab}` is a right derived functor
of the supported-sections endofunctor `𝒢 ↦ i_*ℋ_Z(𝒢)`, on the right of the composite
`H_Z ⋙ i_*`; the two units are built by the same recipe, and
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRealizedCompPushforwardIso` is what
separates them.

This is the hypothesis of
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app`. -/
private theorem unitComparison :
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
        X Z hZ
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
        X Z hZ
    ∀ K : HomotopyCategory
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ),
      (derivedAbelianSupportedPushforwardUnit X Z hZ).app K =
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory
              (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).inv
                (ComplexShape.up ℤ)).app K) ≫
          (postcomposeUnit (abelianSupportedSectionsOnClosed X Z hZ)
            (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
            (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)).app K := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  intro K
  have hsplit : (derivedAbelianSupportedPushforwardUnit X Z hZ).app K =
      (DerivedCategory.Qh.map
              ((NatTrans.mapHomotopyCategory
                (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).inv
                  (ComplexShape.up ℤ)).app K) ≫
            CategoryStruct.id _ ≫
              (abelianClosedPushforward Z).mapDerivedCategoryFactorsh.inv.app
                  (((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory
                    (ComplexShape.up ℤ)).obj K) ≫
                CategoryStruct.id _) ≫
        (abelianClosedPushforward Z).mapDerivedCategory.map
            ((derivedAbelianSupportedSectionsOnClosedUnit X Z hZ).app K) ≫
          CategoryStruct.id _ := rfl
  exact hsplit.trans (unit_formal _ _ _ _ _ _ _ rfl rfl rfl
    (postcomposeUnit_app (abelianSupportedSectionsOnClosed X Z hZ)
      (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
      (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ) K))

/-- The derived pushforward of the supported sections is a right derived functor of the
composite `H_Z ⋙ i_*`, with the unit built by post-composition. -/
private theorem isRightDerivedFunctor_derivedAbelianSupportedPushforward :
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
        X Z hZ
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
        X Z hZ
    letI := abelianClosedPushforward_preservesHomology Z hZ
    (derivedAbelianSupportedPushforward X Z hZ).IsRightDerivedFunctor
      (postcomposeUnit (abelianSupportedSectionsOnClosed X Z hZ)
        (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
        (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ))
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  exact isRightDerivedFunctor_postcompose (abelianSupportedSectionsOnClosed X Z hZ)
    (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ) enoughKInjectives

/-- The same statement for the composite spelling `Rw ⋙ i_*.mapDerivedCategory`. -/
private theorem isRightDerivedFunctor_derivedSections_comp_mapDerivedCategory :
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
        X Z hZ
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
        X Z hZ
    letI := abelianClosedPushforward_preservesHomology Z hZ
    (derivedAbelianSupportedSectionsOnClosed X Z hZ ⋙
        (abelianClosedPushforward Z).mapDerivedCategory).IsRightDerivedFunctor
      (postcomposeUnit (abelianSupportedSectionsOnClosed X Z hZ)
        (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
        (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ))
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  exact isRightDerivedFunctor_postcompose (abelianSupportedSectionsOnClosed X Z hZ)
    (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ) enoughKInjectives

/-- **The bridge of `i_* R𝓗_Z^{ab}` read as a right derived functor of `H_Z ⋙ i_*` splits into
three factors**: the exact direct image pulled out of the cohomology of the derived category, the
bridge for `H_Z` under the direct image, and the direct image pulled out of the `ℕ`-indexed right
derived functor.  This is
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app`, with the
composite written as `derivedAbelianSupportedPushforward`. -/
private theorem postCompSplit :
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
        X Z hZ
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
        X Z hZ
    letI := abelianClosedPushforward_preservesHomology Z hZ
    letI := isRightDerivedFunctor_derivedAbelianSupportedPushforward X Z hZ
    (singleCompDerivedCompHomologyIsoRightDerived
        (abelianSupportedSectionsOnClosed X Z hZ ⋙ abelianClosedPushforward Z)
        (derivedAbelianSupportedPushforward X Z hZ)
        (postcomposeUnit (abelianSupportedSectionsOnClosed X Z hZ)
          (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
          (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ))
        enoughKInjectives n).hom.app G =
      ((abelianClosedPushforward Z).mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
          ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)) ≫
        (abelianClosedPushforward Z).map
            ((abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G) ≫
          ((abelianSupportedSectionsOnClosed X Z hZ).rightDerivedCompIso
            (abelianClosedPushforward Z) n).inv.app G := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  let := abelianClosedPushforward_preservesHomology Z hZ
  let := isRightDerivedFunctor_derivedAbelianSupportedPushforward X Z hZ
  let := isRightDerivedFunctor_derivedSections_comp_mapDerivedCategory X Z hZ
  exact singleCompDerivedCompHomologyIsoRightDerived_postComp_app
    (abelianSupportedSectionsOnClosed X Z hZ) (abelianClosedPushforward Z)
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ) enoughKInjectives n G

/-- **The first two of those three factors are the abelian model comparison.**  This is
`Stacks.Cohomology.AbelianModelComparison.abelianModelComponent_hom` with its leading factor read
through `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` rather than
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`; the two are the same isomorphism,
by `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`.
-/
private theorem modelSplit :
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
        X Z hZ
    letI :=
      Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
        X Z hZ
    (abelianModelComponent X Z hZ n G).hom =
      ((abelianClosedPushforward Z).mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
          ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)) ≫
        (abelianClosedPushforward Z).map
          ((abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G) := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  have hiso : (abelianClosedPushforward Z).mapDerivedCategoryHomologyIso (n : ℤ) =
      (abelianClosedPushforward Z).mapDerivedCategoryHomologyFunctorIso (n : ℤ) :=
    Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso _ _
  have hpush : ((abelianClosedPushforward Z).mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
        ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)) =
      (abelianPushHomologySingleIso X Z hZ (n : ℤ) G).hom :=
    congrArg (fun z => z.hom.app
      ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj
        ((DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G))) hiso
  exact (abelianModelComponent_hom X Z hZ n G).trans
    (congrArg (fun z => z ≫ (abelianClosedPushforward Z).map
      ((abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G)) hpush.symm)

/-- **The third factor, followed by the degree-`n` right derived functor of the comparison of the
two spellings, is the identification of the two models of `i_*ℋ ⁿ_Z`.**  This is
`Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` at
`abelianLocalCohomologySheafPushforwardIso`. -/
private theorem targetSplit :
    letI := abelianClosedPushforward_preservesHomology Z hZ
    (abelianLocalCohomologySheafPushforwardIso Z hZ n).hom.app G =
      ((abelianSupportedSectionsOnClosed X Z hZ).rightDerivedCompIso
          (abelianClosedPushforward Z) n).inv.app G ≫
        (NatTrans.rightDerived
          (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).hom n).app G := by
  let := abelianClosedPushforward_preservesHomology Z hZ
  exact moduleComparison_rightDerivedCompIso_hom_app (abelianSupportedSectionsOnClosed X Z hZ)
    (abelianClosedPushforward Z) (abelianSupportedSections Z)
    (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ) n G

/-! ### The two models agree with the direct image folded in, through the endofunctor's bridge -/

/-- **The canonical bridge of `i_* R𝓗_Z^{ab}` is the abelian model comparison followed by the
identification of the two models of `i_*ℋ ⁿ_Z`.**

For a closed subset `Z` of a ringed space `X`, a degree `n : ℕ` and an abelian sheaf `𝒢` on `X`,
the bridge `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` of
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward` — which identifies
`H ⁿ(i_* R𝓗_Z^{ab}(𝒢[0]))` with the degree-`n` right derived functor of the supported-sections
endofunctor `𝒢 ↦ i_*ℋ_Z(𝒢)` — is
`Stacks.Cohomology.AbelianModelComparison.abelianModelComponent`, which lands in `i_*ℋ ⁿ_Z(𝒢)`
with the cohomology sheaf taken on `Z`, followed by
`abelianLocalCohomologySheafPushforwardIso`.

There is no hypothesis beyond `hZ`, and none whatsoever on `𝒢`. -/
theorem abelianSupportedPushforwardBridge_hom_app :
    (singleCompDerivedCompHomologyIsoRightDerived
        (abelianSupportedSections Z) (derivedAbelianSupportedPushforward X Z hZ)
        (derivedAbelianSupportedPushforwardUnit X Z hZ) enoughKInjectives n).hom.app G =
      (abelianModelComponent X Z hZ n G).hom ≫
        (abelianLocalCohomologySheafPushforwardIso Z hZ n).hom.app G := by
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
      X Z hZ
  let :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X Z hZ
  let := abelianClosedPushforward_preservesHomology Z hZ
  let := isRightDerivedFunctor_derivedAbelianSupportedPushforward X Z hZ
  have hsource := singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app
    (abelianSupportedSectionsOnClosed X Z hZ ⋙ abelianClosedPushforward Z)
    (abelianSupportedSections Z) (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ)
    (derivedAbelianSupportedPushforward X Z hZ)
    (postcomposeUnit (abelianSupportedSectionsOnClosed X Z hZ)
      (abelianClosedPushforward Z) (derivedAbelianSupportedSectionsOnClosed X Z hZ)
      (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ))
    (derivedAbelianSupportedPushforwardUnit X Z hZ) enoughKInjectives
    (unitComparison X Z hZ) n G
  exact hsource.trans
    ((congrArg (fun t => t ≫ (NatTrans.rightDerived
        (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).hom n).app G)
      (postCompSplit X Z hZ n G)).trans
      (assemble _ _ _ _ _ _ (modelSplit X Z hZ n G) (targetSplit X Z hZ n G)))

/-- **The abelian model comparison is the canonical bridge of `i_* R𝓗_Z^{ab}` followed by the
identification of the two models inverted**, the other reading of
`abelianSupportedPushforwardBridge_hom_app`. -/
theorem abelianModelComponent_hom_comp_pushforwardIso :
    (abelianModelComponent X Z hZ n G).hom =
      (singleCompDerivedCompHomologyIsoRightDerived
          (abelianSupportedSections Z) (derivedAbelianSupportedPushforward X Z hZ)
          (derivedAbelianSupportedPushforwardUnit X Z hZ) enoughKInjectives n).hom.app G ≫
        (abelianLocalCohomologySheafPushforwardIso Z hZ n).inv.app G :=
  (Iso.eq_comp_inv ((abelianLocalCohomologySheafPushforwardIso Z hZ n).app G)).mpr
    (abelianSupportedPushforwardBridge_hom_app X Z hZ n G).symm

end Stacks.Cohomology.SupportedComplexes

end
