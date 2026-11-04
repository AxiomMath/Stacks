module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidTwoGenerator
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidOneGenerator
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFlatProperDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidZariskiStack
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorEquivalence

/-!
# Stacks Tag 0EXE: finite locally free Frobenius-colimit modules form an h stack in groupoids

Let `p` be a prime and `S` a scheme in characteristic `p`.  The category fibred in groupoids
`p : 𝒮 ⟶ (Sch/S)_h` of Stacks Tag 0EXE, `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration`,
has as fibre over `U` the groupoid of finite locally free `colim_F 𝒪_U`-modules.  It is a stack in
groupoids for the h topology.

The proof is the source's: the three conditions of Stacks 0EX9 are checked.

* Condition (1), Zariski descent:
  `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isZariskiStackInGroupoids`.
* Condition (2), effective descent along a surjective flat proper morphism of finite presentation
  onto an affine object (fppf descent of finite locally free modules, Stacks 023T and 05B2, carried
  to the Frobenius colimits through Stacks 0EXB):
  `isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration`.
* Condition (3) for the squares of Example 0EVG is Stacks Tag 0EXC:
  `AlgebraicGeometry.isOneGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration`.
* Condition (3) for the squares of Example 0EVH is Stacks Tag 0EXD,
  `AlgebraicGeometry.isEquivalence_twoGeneratorFrobeniusColimitComparison`, carried from the model
  square to the squares of `(Sch/S)_h` and to the fibres of the fibration by
  `isTwoGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration_of_model`.

They are assembled by
`AlgebraicGeometry.isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_conditions`, which
is Stacks 0EX9, `AlgebraicGeometry.BigHOver.isStackInGroupoids_of_generatorSquares`.

The final assertion of Stacks Tag 0EXE, that for `U` quasi-compact and quasi-separated `𝒮_U` is
`colim_F Vect(U)`, is registered separately as
`AlgebraicGeometry.frobeniusVectorBundleGroupoidFiberEquivCoreColimitVect`.

## Main results

* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isStackInGroupoids`: **Stacks Tag
  0EXE**, the stack-in-groupoids assertion, for an arbitrary scheme `S` in characteristic `p`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 0EXE.** Let `p` be a prime number and let `S` be a scheme in
characteristic `p`. Then the category fibred in groupoids `p : 𝒮 ⟶ (Sch/S)_h` whose fibre category
over `U` is the category of finite locally free `colim_F 𝒪_U`-modules over `U` (with its
isomorphisms) is a stack in groupoids.

Here `(Sch/S)_h` is the big h site `AlgebraicGeometry.BigHOver B S hS` of an arbitrary big h site
`B` containing `S`, and "stack in groupoids" is Stacks 02ZI for its h topology. -/
@[stacks 0EXE "stack in groupoids"]
theorem frobeniusVectorBundleGroupoidFibration_isStackInGroupoids
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
    (hpS : IsInCharacteristic S p) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsStackInGroupoids.{u + 1}
      (BigHOver.topology B S hS) :=
  isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_conditions B S hS p hpS
    (frobeniusVectorBundleGroupoidFibration_isZariskiStackInGroupoids B S hS p hpS)
    (isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration
      B S hS p hpS)
    (isOneGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration B S hS p hpS)
    (fun A _ f₁ f₂ hpA => isEquivalence_twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA)

end AlgebraicGeometry

end
