module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRingChangeSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes

/-!
# The derived direct image of a complex read over `(f ∘ g)^{-1}𝒪_S`

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. The relative de Rham complex `Ω^•_{X/S}`
is a complex of `(f ∘ g)^{-1}𝒪_S`-modules, and the graded pieces of its filtration of Section 0FMK
are obtained from complexes of `f^{-1}𝒪_Y`-modules by restriction of scalars along
`(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`.

We show that the derived pushforward `derivedRelativePushforward f g` along `relativeBase f g` is
the derived pushforward `derivedPushforward (relativeBase f g)`, and that the derived functor of
the restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, which is exact, is computed
degreewise.

## Main definitions

* `Stacks.DeRhamSmooth.derivedCoefficientRestrictionQIso`:
  `R(\text{res})_*(QC^•) ≅ Q(\text{res}(C^•))`, the degreewise computation of the derived
  restriction of scalars.

## Main results

* `Stacks.DeRhamSmooth.derivedRelativePushforward_eq`: the two derived pushforwards on
  `(f ∘ g)^{-1}𝒪_S`-modules agree.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes (derivedPushforwardQIso)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The derived direct image `derivedRelativePushforward f g` of `(f ∘ g)^{-1}𝒪_S`-modules is the
derived pushforward along `relativeBase f g`. -/
theorem derivedRelativePushforward_eq :
    derivedRelativePushforward f g = derivedPushforward (relativeBase f g) :=
  rfl

/-- The derived restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, applied to the image of
a complex `C` in the derived category, is the image of the restriction of scalars of `C` applied
degreewise. -/
def derivedCoefficientRestrictionQIso (C : CochainComplex (Modules (inverseImageBase f)) ℤ) :
    (derivedPushforward (coefficientRingChange f g)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI : PreservesFiniteColimits (modulePushforward (coefficientRingChange f g)) :=
    preservesFiniteColimits_coefficientRestriction f g
  derivedPushforwardQIso (coefficientRingChange f g) C

end Stacks.DeRhamSmooth

end
