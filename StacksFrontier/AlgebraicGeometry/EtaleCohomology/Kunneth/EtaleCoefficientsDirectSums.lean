module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackAsATriangulatedFunctor
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.DirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# Exactness and direct sums for `f⁻¹`, `Rf_*` and `⊗^L` on `D(X_étale, Λ)`

On the derived categories `D(X_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients`, the
proof of [Stacks, Tag 0F1N] reduces to two properties of the functors of the Künneth section:
they are exact functors of triangulated categories, and they commute with direct sums. This file
records them for the inverse and direct images and the derived tensor product:

* `f⁻¹` is exact (Stacks 06YY) and, as a left adjoint, commutes with all colimits;
* `Rf_*` is exact, as the right adjoint of an exact functor;
* `⊗^L_Λ` commutes with direct sums in each variable (Stacks 06YU). In the second variable this
  is
  `Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor`;
  the first variable is reduced to it through the identification of `⊗^L_Λ` with the tensor
  product of the symmetric monoidal structure of Stacks 0FPT on `D(X_étale, Λ)`, whose braiding
  exchanges the two variables. Its exactness in each variable is part of the structure
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.

That `Rf_*` commutes with direct sums for `f` quasi-compact and quasi-separated with `cd(f) < ∞`
and `Λ` torsion ([Stacks, Tag 0F11] (1)) is
`Stacks.EtaleCohomology.EtaleCoefficients.preservesColimitsOfShape_pushforward`.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* The instances `pullbackCommShift`, `pullback_isTriangulated`, `pushforwardCommShift`,
  `pushforward_isTriangulated`, `adjunction_commShift`.
* `preservesColimitsOfShape_pullback`, `preservesColimitsOfShape_tensor_obj`,
  `preservesColimitsOfShape_tensor_flip_obj`.

## References

* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Exactness -/

section Triangulated

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f⁻¹` commutes with the shift (Stacks 06YY). -/
@[instance_reducible]
def pullbackCommShift : (pullback Λ f).CommShift ℤ :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackCommShift (ringedToposHom Λ f)
    (isMorphismOfSites_ringedToposHom Λ f)

attribute [instance] pullbackCommShift

/-- `f⁻¹` is an exact functor of triangulated categories (Stacks 06YY). -/
instance pullback_isTriangulated : (pullback Λ f).IsTriangulated :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullback_isTriangulated_of_isMorphismOfSites
    (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ f)

/-- `Rf_*` commutes with the shift, as the right adjoint of `f⁻¹`. -/
@[instance_reducible]
def pushforwardCommShift : (pushforward Λ f).CommShift ℤ :=
  (adjunction Λ f).rightAdjointCommShift ℤ

attribute [instance] pushforwardCommShift

/-- The adjunction `f⁻¹ ⊣ Rf_*` is compatible with the shifts. -/
instance adjunction_commShift : (adjunction Λ f).CommShift ℤ :=
  (adjunction Λ f).commShift_of_leftAdjoint ℤ

/-- `Rf_*` is an exact functor of triangulated categories, as the right adjoint of one. -/
instance pushforward_isTriangulated : (pushforward Λ f).IsTriangulated :=
  (adjunction Λ f).isTriangulated_rightAdjoint

end Triangulated

/-! ### Direct sums for `f⁻¹` and `⊗^L` -/

section DirectSums

/-- `f⁻¹` commutes with all colimits, being a left adjoint. -/
instance preservesColimitsOfShape_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Type*)
    [Category J] : PreservesColimitsOfShape J (pullback Λ f) :=
  have := (adjunction Λ f).leftAdjoint_preservesColimits
  inferInstance

variable (X : Scheme.{u})

/-- `E ⊗^L_Λ -` commutes with direct sums (Stacks 06YU). -/
theorem preservesColimitsOfShape_tensor_obj (I : Type (u + 1)) (E : DerivedModules Λ X) :
    PreservesColimitsOfShape (Discrete I) ((tensor Λ X).obj E) :=
  Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor
    _ I E

/-- `- ⊗^L_Λ E` commutes with direct sums (Stacks 06YU): through the identification of `⊗^L_Λ`
with the tensor product of the symmetric monoidal structure of Stacks 0FPT on `D(X_étale, Λ)`,
whose braiding exchanges the two variables, this is the case of the second variable. -/
theorem preservesColimitsOfShape_tensor_flip_obj (I : Type (u + 1)) (E : DerivedModules Λ X) :
    PreservesColimitsOfShape (Discrete I) ((tensor Λ X).flip.obj E) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (ringedTopos Λ X).O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric (ringedTopos Λ X).O
  have := preservesColimitsOfShape_tensor_obj Λ X I E
  have : PreservesColimitsOfShape (Discrete I) (MonoidalCategory.tensorLeft E) :=
    preservesColimitsOfShape_of_natIso
      ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso (ringedTopos Λ X).O).app
        E).symm
  have : PreservesColimitsOfShape (Discrete I) (MonoidalCategory.tensorRight E) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight E)
  exact preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorRight E)
    (((flipFunctor _ _ _).mapIso
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso (ringedTopos Λ X).O)).app E)

end DirectSums

end Stacks.EtaleCohomology.EtaleCoefficients
