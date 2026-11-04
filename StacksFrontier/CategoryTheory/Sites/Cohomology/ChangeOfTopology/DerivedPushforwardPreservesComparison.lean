module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation
public import StacksFrontier.Homology.DerivedIndexing.Extend
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image preserves the bounded below comparison subcategory

In the situation of Stacks 0EZ3, let `f : X ⟶ Y` be a morphism in the distinguished class `P`
and let `K'` be an object of `D⁺(C_τ'/X)` all of whose cohomology sheaves lie in the weak Serre
class `𝒜'_X`. This file proves that the total right derived direct image `Rf_{τ',*} K'` again
has all its cohomology sheaves in `𝒜'_Y`, that is, that derived direct image carries
`D⁺_{𝒜'_X}` into `D⁺_{𝒜'_Y}`.

The argument is the source's, and it is carried out for an arbitrary additive functor in
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`: choose a
Cartan--Eilenberg resolution of a bounded below cochain complex representing `K'`; applying
`f_{τ',*}` degreewise gives a double complex which is bounded in both directions, so its total
complex exists and the spectral sequence of its filtration by columns converges. The second page
of that spectral sequence is `E_2^{p,q} = R^p f_{τ',*} H^q(K')`, which lies in `𝒜'_Y` by the
hypothesis `weakSerre_rightDerived_relocalizationPushforward` of the situation, and `𝒜'_Y` is a
weak Serre class, hence closed under the subquotients and extensions through which the abutment
is built from the second page. The abutment is `H^{p+q}(Rf_{τ',*}K')`, which therefore lies in
`𝒜'_Y` as well.

All that is left here is to supply that dévissage with the functor, the two weak Serre classes
and the hypothesis on the right derived functors; the hypothesis of the situation is stated with
Mathlib's `Functor.rightDerived`, which is the indexing the dévissage asks for.

## Main results

* `Stacks.ComparingTopologies.rightDerivedPushforward_mem_derivedCategoryBPlus`: derived
  direct image along a morphism of `P` preserves `D⁺_{𝒜'}`.

## Implementation notes

This is one clause of Stacks 0EZF, which also asserts the conditions `(V_n)`, the
isomorphism `K' ≅ Rε_{X,*} ε_X^{-1} K'` of its part (1), and the base-change identification
`ε_Y^{-1} Rf_{τ',*} K' = Rf_{τ,*} ε_X^{-1} K'` of its part (2). Those are proved elsewhere —
the base-change identification in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardBaseChange` —
and the attribute on the result below is part-qualified accordingly: it carries the membership
half of part (2) of the covering set and nothing else.

The subcategory `D⁺_{𝒜'}` is `DerivedCategoryB.derivedCategoryBPlus` applied to the underlying
object of `DerivedCategory.Plus`, and derived direct image is the total right derived functor
`Functor.rightDerivedFunctorPlus` of the relocalization direct image on the coarser site.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.Limits Opposite

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

section Implementation

-- NO `exists_plusQ_obj_iso` HERE. It stated exactly the public
-- `DerivedCategory.Plus.exists_iso_Q_obj`
-- (`StacksFrontier/Algebra/Homology/DerivedCategory/WeakSerreClassRightDerivedFunctorPlus.lean`),
-- which this module now imports and whose dévissage uses it directly.

/-- The content of `rightDerivedPushforward_mem_derivedCategoryBPlus`, which is the dévissage
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj` by the spectral
sequence of a Cartan--Eilenberg resolution, applied to the relocalization direct image: the
hypothesis of that dévissage on the right derived functors is the field
`weakSerre_rightDerived_relocalizationPushforward` of the situation. -/
private theorem rightDerivedPushforward_mem_derivedCategoryBPlus_aux
    (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (hf : S.morphismProperty f)
    (K : DerivedCategory.Plus
      (Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}))
    (hK : DerivedCategoryB.derivedCategoryBPlus (S.weakSerre X) K.obj) :
    DerivedCategoryB.derivedCategoryBPlus (S.weakSerre Y)
      ((((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
          (S.coarseCoverage.toGrothendieck.over X)
          (S.coarseCoverage.toGrothendieck.over Y)).rightDerivedFunctorPlus.obj K).obj) :=
  let : (S.weakSerre X).IsWeakSerreClass := S.weakSerreClass X
  let : (S.weakSerre Y).IsWeakSerreClass := S.weakSerreClass Y
  Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    ((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
      (S.coarseCoverage.toGrothendieck.over X) (S.coarseCoverage.toGrothendieck.over Y))
    (S.weakSerre X) (S.weakSerre Y)
    (fun M hM p => S.weakSerre_rightDerived_relocalizationPushforward f hf M hM p) K hK.2

end Implementation

/-- **Stacks 0EZF**, the first assertion of part (2). In a cohomology comparison situation,
total right derived direct image along a morphism of the distinguished class `P` carries
`D⁺_{𝒜'_X}` into `D⁺_{𝒜'_Y}`.

No hypothesis beyond those of the tag is used: in particular the vanishing conditions `(V_n)`,
which the tag asserts first, are not needed for this half. See the implementation notes for the
other clauses of the tag and where they live. -/
@[stacks 0EZF "part (2), membership: `R f_{τ',*}` carries `D⁺_{𝒜'_X}` into `D⁺_{𝒜'_Y}`"]
theorem rightDerivedPushforward_mem_derivedCategoryBPlus
    (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (hf : S.morphismProperty f)
    (K : DerivedCategory.Plus
      (Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}))
    (hK : DerivedCategoryB.derivedCategoryBPlus (S.weakSerre X) K.obj) :
    DerivedCategoryB.derivedCategoryBPlus (S.weakSerre Y)
      ((((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
          (S.coarseCoverage.toGrothendieck.over X)
          (S.coarseCoverage.toGrothendieck.over Y)).rightDerivedFunctorPlus.obj K).obj) :=
  rightDerivedPushforward_mem_derivedCategoryBPlus_aux S f hf K hK

end Stacks.ComparingTopologies
